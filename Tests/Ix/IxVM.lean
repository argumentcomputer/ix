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
  ("HEq",                                                                1_266_959),
  ("HEq.rec",                                                            1_731_811),
  ("Eq.rec",                                                             1_628_183),
  ("Nat",                                                                1_378_982),
  ("Nat.add",                                                            5_866_305),
  ("Nat.add_comm",                                                       23_573_734),
  ("Nat.decEq",                                                          33_296_554),
  ("Nat.decLe",                                                          89_190_557),
  ("Nat.sub_le_of_le_add",                                               241_662_332),
  -- Newly-unlocked targets (level_leq Géran normalize).
  ("Trans.mk",                                                           1_973_235),
  ("Array.append_assoc",                                                 1_420_612_581),
  ("Vector.append",                                                      1_450_636_681),
  -- Primitive reduction theorems (`IxVMPrim`)
  ("IxVMPrim.nat_add_lit",                                               11_942_256),
  ("IxVMPrim.nat_sub_lit",                                               13_585_666),
  ("IxVMPrim.nat_mul_lit",                                               9_751_781),
  ("IxVMPrim.nat_mul_big",                                               9_641_877),
  ("IxVMPrim.nat_div_lit",                                               169_759_695),
  ("IxVMPrim.nat_mod_lit",                                               172_924_236),
  ("IxVMPrim.nat_succ_lit",                                              3_252_903),
  ("IxVMPrim.nat_pred_lit",                                              5_723_974),
  ("IxVMPrim.nat_gcd_lit",                                               276_570_901),
  ("IxVMPrim.nat_land_lit",                                              454_075_744),
  ("IxVMPrim.nat_lor_lit",                                               454_180_273),
  ("IxVMPrim.nat_xor_lit",                                               457_524_569),
  ("IxVMPrim.nat_shl_lit",                                               13_638_647),
  ("IxVMPrim.nat_shr_lit",                                               171_158_166),
  ("IxVMPrim.nat_pow_big",                                                40_140_538),
  ("IxVMPrim.nat_beq_lit",                                               10_299_628),
  ("IxVMPrim.nat_ble_lit",                                               9_745_047),
  ("IxVMPrim.nat_dec_le",                                                91_613_507),
  ("IxVMPrim.nat_dec_lt",                                                92_974_969),
  ("IxVMPrim.nat_dec_eq",                                                38_659_146),
  ("IxVMPrim.str_size_lit",                                              320_266_989),
  ("IxVMPrim.bv_to_nat_lit",                                             262_435_393),
  -- Mutual block + multi-member recursors
  ("IxVMInd.Even",                                                       11_288_706),
  ("IxVMInd.Odd",                                                        11_095_224),
  ("IxVMInd.Even.rec",                                                   13_465_827),
  ("IxVMInd.Odd.rec",                                                    13_462_266),
  -- Nested inductive + aux recursor (Tree.mk : List Tree → Tree)
  ("IxVMInd.Tree",                                                       1_786_697),
  ("IxVMInd.Tree.rec",                                                   2_713_344),
  -- Aux dedup: distinct spec_params on one external inductive (3 motives).
  ("IxVMInd.DedupM",                                                     2_758_628),
  ("IxVMInd.DedupM.rec",                                                 4_064_079),
  -- Aux dedup de-lift guard: equal spec_params at field depths 0 and 2.
  ("IxVMInd.DepthM",                                                     2_192_684),
  ("IxVMInd.DepthM.rec",                                                 3_328_375),
  -- Edge cases from prelude
  ("String.Internal.append",                                             319_147_017),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec",         476_973_098),
  -- Aux recursor with transitively-nested inductives (Syntax → Array Syntax
  -- → List Syntax); shard 53 regression driver.
  ("Lean.Syntax.rec",                                                    333_971_638),
  -- Evaporated-aux canonicalization (Tests/Ix/Compile/Mutual.lean AuxDedup*):
  -- SCC splitting strands `rec_N` auxes whose spec-param inductives moved to
  -- other SCCs; their claims alias the external inductive's recursor
  -- (`List.rec`) — hence the identical pin on all four evaporated entries,
  -- whose claims are literally the same `List.rec` closure. AuxDedupMixed
  -- mixes one genuine canonical aux (`M.rec_1`, over `List M`) with one
  -- evaporated alias (`M.rec_2`, over `List B`).
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A",             2_129_800),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec",         2_442_791),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1",       1_919_602),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2",       1_919_602),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1",       1_919_602),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M",         2_162_714),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec",     3_210_456),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1",   3_212_241),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2",   1_919_602),
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
