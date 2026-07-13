module

public import Ix.Meta
public import Ix.AssumptionTree
public import Ix.IxVM.ClaimHarness
public import Tests.Aiur.Common

open IxVM.ClaimHarness LSpec

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
    runners against the `verify_claim` Aiur entrypoint, driving a
    `Ix.Claim.check addr none` claim.
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
-- Synthetic: exercises `klimbs_pow` at a non-trivial exponent so the cost
-- of the current O(exp) recursive implementation shows up in the FFT pin.
-- Sized to terminate under typical caps with the current O(exp) body — a
-- proxy for the eventual binary-exponentiation rewrite.
set_option exponentiation.threshold 65536 in
set_option maxRecDepth 65536 in
public theorem nat_pow_big : (2 ^ 16384 : Nat) - (2 ^ 16384) = 0 := rfl

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

-- Aux dedup key: two nested occurrences of the SAME external inductive
-- with DISTINCT spec_params. flat must be [DedupM, Bar2⟨DedupM,Nat⟩,
-- Bar2⟨DedupM,Bool⟩] (3 motives); a dedup keyed on the base const idx
-- alone collapses the two Bar2 auxes.
public inductive Bar2 (α β : Type) where
  | mk : α → Bar2 α β

public inductive DedupM where
  | mk : Bar2 DedupM Nat → Bar2 DedupM Bool → DedupM

-- De-lift guard: the SAME spec_param (`Bar1 (DepthM α)`) at field
-- depths 0 and 2. In the un-opened de Bruijn view the block-param ref
-- is BVar(0) vs BVar(2); without de-lifting to the param context a
-- structural/ptr dedup would see two distinct auxes where flat must
-- have exactly one.
public inductive Bar1 (α : Type) where
  | mk : α → Bar1 α

public inductive DepthM (α : Type) where
  | mk : Bar1 (DepthM α) → Nat → Bar1 (DepthM α) → DepthM α

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

/-- Build a `verify_claim` invocation for `name` driving the claim
    `Ix.Claim.check addr none` — fully transitive typecheck of the
    target's closure. -/
public def kernelCheck (name : Lean.Name) (env : Lean.Environment) :
    IO AiurTestCase := do
  let ixonEnv ← loadIxonEnv name env
  let target ← lookupAddr ixonEnv name
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv (Ix.Claim.check target none)
  pure { functionName := witness.funcName, label := s!"Kernel check {name}"
         input := witness.input, inputIOBuffer := witness.inputIOBuffer
         expectedIOBuffer := witness.inputIOBuffer
         interpret := false, executionOnly := true }

/-- Kernel-check targets paired with their expected total FFT cost
    (rounded to `Nat`). Names listed as strings to dodge name-quotation
    parser issues with numeric components (e.g. `_private...0...`).

    The pinned cost makes any kernel change that shifts FFT cost cause a
    test failure, forcing a manual bump here. Failures report the
    observed cost in the message so it can be pasted back. -/
private def kernelCheckEntries : List (String × Nat) := [
  -- Stdlib
  ("HEq",                                                                1_687_513),
  ("HEq.rec",                                                            2_634_878),
  ("Eq.rec",                                                             2_529_273),
  ("Nat",                                                                1_823_329),
  ("Nat.add",                                                            12_560_324),
  ("Nat.add_comm",                                                       52_451_949),
  ("Nat.decEq",                                                          66_000_939),
  ("Nat.decLe",                                                          183_980_659),
  ("Nat.sub_le_of_le_add",                                               497_809_853),
  -- Newly-unlocked targets (level_leq Géran normalize).
  ("Trans.mk",                                                           2_804_310),
  ("Array.append_assoc",                                                 2_469_036_319),
  ("Vector.append",                                                      2_535_471_175),
  -- Primitive reduction theorems (`IxVMPrim`)
  ("IxVMPrim.nat_add_lit",                                               26_840_933),
  ("IxVMPrim.nat_sub_lit",                                               32_407_346),
  ("IxVMPrim.nat_mul_lit",                                               23_699_996),
  ("IxVMPrim.nat_mul_big",                                               23_162_723),
  ("IxVMPrim.nat_div_lit",                                               354_160_359),
  ("IxVMPrim.nat_mod_lit",                                               362_156_491),
  ("IxVMPrim.nat_succ_lit",                                              7_015_630),
  ("IxVMPrim.nat_pred_lit",                                              14_084_435),
  ("IxVMPrim.nat_gcd_lit",                                               583_133_276),
  ("IxVMPrim.nat_land_lit",                                              981_213_352),
  ("IxVMPrim.nat_lor_lit",                                               981_900_122),
  ("IxVMPrim.nat_xor_lit",                                               989_652_326),
  ("IxVMPrim.nat_shl_lit",                                               33_389_726),
  ("IxVMPrim.nat_shr_lit",                                               358_936_157),
  ("IxVMPrim.nat_pow_big",                                                69_756_731),
  ("IxVMPrim.nat_beq_lit",                                               23_183_422),
  ("IxVMPrim.nat_ble_lit",                                               21_526_671),
  ("IxVMPrim.nat_dec_le",                                                190_151_568),
  ("IxVMPrim.nat_dec_lt",                                                193_962_813),
  ("IxVMPrim.nat_dec_eq",                                                79_095_341),
  ("IxVMPrim.str_size_lit",                                              692_750_494),
  ("IxVMPrim.bv_to_nat_lit",                                             555_210_880),
  -- Mutual block + multi-member recursors
  ("IxVMInd.Even",                                                       24_876_261),
  ("IxVMInd.Odd",                                                        24_637_719),
  ("IxVMInd.Even.rec",                                                   30_328_475),
  ("IxVMInd.Odd.rec",                                                    30_325_959),
  -- Nested inductive + aux recursor (Tree.mk : List Tree → Tree)
  ("IxVMInd.Tree",                                                       2_561_784),
  ("IxVMInd.Tree.rec",                                                   4_751_390),
  -- Aux dedup: distinct spec_params on one external inductive (3 motives).
  ("IxVMInd.DedupM",                                                     4_608_126),
  ("IxVMInd.DedupM.rec",                                                 7_702_744),
  -- Aux dedup de-lift guard: equal spec_params at field depths 0 and 2.
  ("IxVMInd.DepthM",                                                     3_480_328),
  ("IxVMInd.DepthM.rec",                                                 6_125_812),
  -- Edge cases from prelude
  ("String.Internal.append",                                             685_185_881),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec",         1_029_939_759),
  -- Aux recursor with transitively-nested inductives (Syntax → Array Syntax
  -- → List Syntax); shard 53 regression driver.
  ("Lean.Syntax.rec",                                                    709_841_196),
  -- Evaporated-aux canonicalization (Tests/Ix/Compile/Mutual.lean AuxDedup*):
  -- SCC splitting strands `rec_N` auxes whose spec-param inductives moved to
  -- other SCCs; their claims alias the external inductive's recursor
  -- (`List.rec`) — hence the identical pin on all four evaporated entries,
  -- whose claims are literally the same `List.rec` closure. AuxDedupMixed
  -- mixes one genuine canonical aux (`M.rec_1`, over `List M`) with one
  -- evaporated alias (`M.rec_2`, over `List B`).
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A",             3_422_910),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec",         4_291_814),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1",       3_034_096),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2",       3_034_096),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1",       3_034_096),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M",         3_456_743),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec",     6_012_673),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1",   6_014_651),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2",   3_034_096),
]

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none   => .mkStr acc s

public def kernelChecks (env : Lean.Environment) : IO (List AiurTestCase) :=
  kernelCheckEntries.mapM fun (name, expected) => do
    let tc ← kernelCheck (nameOfString name) env
    pure { tc with expectedFftCost := some expected }

/-! ## Codegen ↔ bytecode parity

Runs the same `AiurTestCase` through both `Toplevel.execute` (Aiur
bytecode interpreter) and `Toplevel.executeIxVM` (codegen'd Rust
kernel), diffing the two triples. Guards against the invariant the
whole codegen design rests on — "generated kernel ≡ interpreter on
the `QueryRecord`" — turning it from reviewed-by-hand into
checked-by-CI. -/
public def runParityCase (compiled : Aiur.CompiledToplevel)
    (tc : AiurTestCase) : TestSeq :=
  let label := tc.label
  let funIdx := compiled.getFuncIdx tc.functionName |>.get!
  match compiled.bytecode.execute funIdx tc.input tc.inputIOBuffer,
        compiled.bytecode.executeIxVM funIdx tc.input tc.inputIOBuffer with
  | .error e, _ => test s!"[parity] bytecode execute succeeds for {label}: {e}" false
  | _, .error e => test s!"[parity] codegen execute succeeds for {label}: {e}" false
  | .ok (bOut, bIO, bQC), .ok (cOut, cIO, cQC) =>
    test s!"[parity] output matches for {label}"    (bOut == cOut)
    ++ test s!"[parity] IOBuffer matches for {label}" (bIO == cIO)
    ++ test s!"[parity] QueryCount matches for {label}"
         (bQC.size == cQC.size &&
          (bQC.zip cQC).all fun (b, c) =>
            b.uniqueRows == c.uniqueRows && b.totalHits == c.totalHits)

/-- Parity fixtures: `kernel_unit_tests` covers the level primitives
    end-to-end with zero IO, and every pinned `kernelCheckEntries`
    constant runs a realistic workload (blake3, ingress, whnf, def-eq,
    recursor gen) against the same IOBuffer under both engines. -/
public def parityCases (env : Lean.Environment) : IO (List AiurTestCase) := do
  let emptyIO : Aiur.IOBuffer := { data := ∅, map := ∅ }
  let kunit : AiurTestCase :=
    { functionName := `kernel_unit_tests, label := "kernel_unit_tests"
      input := #[], inputIOBuffer := emptyIO
      expectedIOBuffer := emptyIO, interpret := false, executionOnly := true }
  let checks ← kernelCheckEntries.mapM fun (name, _) =>
    kernelCheck (nameOfString name) env
  pure (kunit :: checks)

/-! ## Claim variant smoke tests

Each builds an `AiurTestCase` exercising one of the non-`Check-None`
arms of `verify_claim`. All seven tests share a single Ixon env
built once over `{Nat.zero, Nat.add_comm}` — `Nat.zero` for its
small CPrj + Muts (the `Nat` block), `Nat.add_comm` for its Defn
theorems. Loading once instead of per-test cuts Lean→Ixon compile
work by ~6×. -/

/-- Wrap a `ClaimWitness` as an execution-only `AiurTestCase`. -/
private def asTestCase (label : String) (witness : ClaimWitness) : AiurTestCase :=
  { functionName := witness.funcName, label
    input := witness.input, inputIOBuffer := witness.inputIOBuffer
    expectedIOBuffer := witness.inputIOBuffer
    interpret := false, executionOnly := true }

/-- Locate the first constant in `env.consts` whose `ConstantInfo`
    satisfies `pred`, or fail with `IO.userError`. -/
private def findConstWithOrThrow (ixonEnv : Ixon.Env) (label : String)
    (pred : Ixon.ConstantInfo → Bool) : IO (Address × Ixon.ConstantInfo) := do
  for (addr, lc) in ixonEnv.consts do
    if let some c := lc.get? then
      if pred c.info then return (addr, c.info)
  throw <| IO.userError s!"no {label} const found in shared smoke env"

/-- Single-entry HashMap for one `(root, tree)` pairing. -/
private def singletonTrees (tree : Ix.AssumptionTree) :
    Std.HashMap Address Ix.AssumptionTree :=
  ({} : Std.HashMap _ _).insert tree.root tree

/-- `Check` claim with `assumptions = some tree.root` covering every
    transitive dep — kernel ends up checking only the subject. -/
public def claimCheckWithAsm (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let target ← lookupAddr ixonEnv ``Nat.zero
  let closure := closureFrom ixonEnv target
  let depLeaves : Array Address :=
    closure.fold (init := #[]) fun acc a =>
      if a == target then acc else acc.push a
  let some tree := Ix.AssumptionTree.canonical depLeaves
    | throw <| IO.userError "deps unexpectedly empty for Nat.zero"
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.check target (some tree.root)) (singletonTrees tree)
  pure (asTestCase "Claim Check with-asm (Nat.zero)" witness)

/-- `Contains` claim against a synthetic 3-leaf merkle tree. -/
public def claimContains : IO AiurTestCase := do
  let a : Address := ⟨⟨Array.replicate 32 0x11⟩⟩
  let b : Address := ⟨⟨Array.replicate 32 0x22⟩⟩
  let c : Address := ⟨⟨Array.replicate 32 0x33⟩⟩
  let some tree := Ix.AssumptionTree.canonical #[a, b, c]
    | throw <| IO.userError "Contains tree build failed"
  let witness ← IO.ofExcept <| buildClaimWitness ({} : Ixon.Env)
    (Ix.Claim.contains tree.root b) (singletonTrees tree)
  pure (asTestCase "Claim Contains (synthetic 3-leaf)" witness)

/-- `CheckEnv` claim over the shared smoke env. -/
public def claimCheckEnv (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let some tree := envCanonicalTree ixonEnv
    | throw <| IO.userError "envCanonicalTree empty"
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.checkEnv tree.root none) (singletonTrees tree)
  pure (asTestCase "Claim CheckEnv (shared smoke env)" witness)

/-- `Reveal` Defn with `kind` + `safety` only — exercises the
    enum-tag compare path with no Expr hashing. -/
public def claimRevealDefnFields (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Defn"
    fun ci => match ci with | .defn _ => true | _ => false
  let .defn d := info
    | throw <| IO.userError "findConstWith returned non-Defn"
  let revealInfo : Ix.RevealConstantInfo :=
    .defn (some d.kind) (some d.safety) none none none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv (Ix.Claim.reveal comm revealInfo)
  pure (asTestCase "Claim Reveal Defn (kind+safety)" witness)

/-- `Reveal` CPrj — projection idx, cidx, block fields. -/
public def claimRevealCPrj (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "CPrj"
    fun ci => match ci with | .cPrj _ => true | _ => false
  let .cPrj p := info
    | throw <| IO.userError "findConstWith returned non-CPrj"
  let revealInfo : Ix.RevealConstantInfo :=
    .cPrj (some p.idx) (some p.cidx) (some p.block)
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv (Ix.Claim.reveal comm revealInfo)
  pure (asTestCase "Claim Reveal CPrj (all fields)" witness)

/-- `Reveal` Defn `typ` via content-hash binding — exercises the
    Aiur `expr_addr` path against `blake3(putExpr d.typ)` on Lean. -/
public def claimRevealDefnExpr (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Defn"
    fun ci => match ci with | .defn _ => true | _ => false
  let .defn d := info
    | throw <| IO.userError "findConstWith returned non-Defn"
  let typAddr := Address.blake3 (Ixon.runPut (Ixon.putExpr d.typ))
  let revealInfo : Ix.RevealConstantInfo :=
    .defn none none none (some typAddr) none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv (Ix.Claim.reveal comm revealInfo)
  pure (asTestCase "Claim Reveal Defn (typ Expr addr)" witness)

/-- `Reveal` Muts — first component, one variant-appropriate
    field set. -/
public def claimRevealMuts (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Muts"
    fun ci => match ci with | .muts _ => true | _ => false
  let .muts components := info
    | throw <| IO.userError "findConstWith returned non-Muts"
  let some firstMc := components[0]?
    | throw <| IO.userError "Muts components empty"
  let revealMc : Ix.RevealMutConstInfo := match firstMc with
    | .defn d => .defn (some d.kind) (some d.safety) none none none
    | .indc i => .indc (some i.isUnsafe) none none none none none
    | .recr r => .recr (some r.k) (some r.isUnsafe) none none none none none
                       none none
  let revealInfo : Ix.RevealConstantInfo := .muts #[(0, revealMc)]
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv (Ix.Claim.reveal comm revealInfo)
  pure (asTestCase "Claim Reveal Muts (first component)" witness)

/-- All claim-variant smoke tests packaged for the `ixvm` runner.
    Builds the shared Ixon env once and threads it through every
    test. -/
public def claimSmokeTests (env : Lean.Environment) : IO (List AiurTestCase) := do
  let ixonEnv ← loadSharedIxonEnv #[``Nat.zero, ``Nat.add_comm] env
  let t1 ← claimCheckWithAsm ixonEnv
  let t2 ← claimContains
  let t3 ← claimCheckEnv ixonEnv
  let t4 ← claimRevealDefnFields ixonEnv
  let t5 ← claimRevealCPrj ixonEnv
  let t6 ← claimRevealDefnExpr ixonEnv
  let t7 ← claimRevealMuts ixonEnv
  pure [t1, t2, t3, t4, t5, t6, t7]
