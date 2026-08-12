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

-- Limb-boundary iota: Nat.casesOn on a literal ≥ 2^32 forces the kernel's
-- one-layer ctor exposure across a limb boundary, where an unnormalized
-- `klimbs_dec` (trailing zero limb) sends the countdown past zero forever.
public theorem nat_cases_big :
    (match (4294967296 : Nat) with | 0 => (0 : Nat) | n+1 => n) = 4294967295 := rfl

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

-- Universe dedup key: two nested occurrences of one external inductive
-- with the SAME term spec_param at DISTINCT universe instantiations
-- (the phantom universe appears only in the result sort). Lean emits
-- distinct motives — flat must be [UnivM, PhantomBox.{0}⟨UnivM⟩,
-- PhantomBox.{1}⟨UnivM⟩] (3 motives); a dedup keyed on (family, term
-- spec_params) alone collapses the two PhantomBox auxes, and a
-- compute_aux_perm source match that ignores head levels maps both
-- source auxes onto one canonical slot.
public inductive PhantomBox (α : Type 2) : Type (max 2 u) where
  | mk : α → PhantomBox α

public inductive UnivM : Type 2 where
  | mk : PhantomBox.{0} UnivM → PhantomBox.{1} UnivM → UnivM

-- De-lift guard: the SAME spec_param (`Bar1 (DepthM α)`) at field
-- depths 0 and 2. In the un-opened de Bruijn view the block-param ref
-- is BVar(0) vs BVar(2); without de-lifting to the param context a
-- structural/ptr dedup would see two distinct auxes where flat must
-- have exactly one.
public inductive Bar1 (α : Type) where
  | mk : α → Bar1 α

public inductive DepthM (α : Type) where
  | mk : Bar1 (DepthM α) → Nat → Bar1 (DepthM α) → DepthM α

-- Canonical-aux-order marker driver (the Lean.Json.rec bug shape,
-- verified failing on the pre-marker kernel): WrapC/WrapI are
-- same-shaped wrappers over same-shaped containers with different
-- payloads (Char vs Int). The wraps' aux views tie weak through
-- sentinels; pre-marker they resolved by the containers' refinement-
-- class order (payload address), which for this payload pair disagrees
-- with the compile-side order. Only the trailing identity marker
-- (ext applied to spec params, external consts by address) recovers
-- compile order.
public inductive CellC (α : Type) where
  | mk : α → Char → CellC α

public inductive CellI (α : Type) where
  | mk : α → Int → CellI α

public inductive WrapC (α : Type) where
  | mk : CellC α → WrapC α

public inductive WrapI (α : Type) where
  | mk : CellI α → WrapI α

public inductive AuxTie where
  | c : WrapC AuxTie → AuxTie
  | i : WrapI AuxTie → AuxTie

-- Wrapper-hidden index binder (the
-- CategoryTheory.MorphismProperty.ofHoms.rec failure shape, minimized —
-- ~30 mathlib recursors share it): the inductive's declared type is a
-- definitional wrapper (an `abbrev` — the elaborator demands
-- reducibility to accept it, but the declaration stores the wrapper
-- un-unfolded), so the index binder only appears after whnf. The
-- canonical recursor reconstruction collects index domains off that
-- declared type; a structural-only peel meets the `App` node instead of
-- a `Forall` and aborts mid-execution, wrongly rejecting the recursor.
-- Pins the whnf fallback in `collect_index_doms`.
public abbrev PredOver (α : Type) : Type := α → Prop

public inductive HiddenIdx (α : Type) : PredOver α where
  | mk : (a : α) → HiddenIdx α a

-- Theorem-headed iota major (the Rat.instEncodable failure shape,
-- minimized): reducing `And.rec motive minor MAJOR` requires the major
-- to reach `And.intro`, and here the major is a THEOREM constant. The
-- general reducer keeps `Thm` heads stuck, so the iota could not fire,
-- the recursor application stayed stuck, and the check failed with
-- "inferred type is not def-eq to the expected type". Pins
-- `whnf_iota_major`, which unfolds theorems in the major position only.
--
-- Construction: the And proof is written INLINE, so the elaborator's
-- Meta def-eq (which treats theorems as opaque, unlike the kernel) sees
-- `And.rec` over `And.intro` and accepts; `abstractNestedProofs` then
-- lifts the proof out as the auto-theorem `thmMajorUse._proof_1` at
-- declaration time — the same mechanism that produced
-- `Rat.instEncodable._proof_1`. The KERNEL therefore checks
-- `Eq.refl 1 : 1 = 1` against the domain `(And.rec … ._proof_1) = 1`,
-- forcing def-eq `1 ≟ And.rec … thmMajorUse._proof_1` with a Thm-headed
-- major. `And` is used for its subsingleton large elimination: an
-- And.rec whose only reduction path is through the major.
public def thmMajorWant (n : Nat) (_pf : n = 1) : Nat := n

@[expose] public def thmMajorUse : Nat :=
  thmMajorWant
    (And.rec (motive := fun _ => Nat) (fun _ _ => 1)
      (⟨Nat.zero_lt_succ 0, Nat.zero_lt_succ 1⟩ : 0 < 1 ∧ 0 < 2))
    (Eq.refl 1)

-- PARTIALLY APPLIED K-recursor (the second half of the same fix): the
-- K-synthesis gate reads the major straight out of the spine with
-- `list_lookup`, which binds `Cons` irrefutably. Its only caller used to
-- be `try_iota`'s stuck branch, which had already established
-- `major_idx < spine_len`; hoisting the gate ABOVE `try_iota` (needed so
-- a K major is never whnf'd, see `whnf_iota_major`) let a short spine
-- reach that lookup, walk off the end, and abort on `Nil` — surfacing as
-- "no match case for value 1" on two `Std.Tactic.BVDecide` constants.
--
-- `Eq.rec` is the K recursor here (nparams=2, nmotives=1, nminors=1,
-- nindices=1), so the major sits at spine index 5 and the five-argument
-- application below is exactly one short. Stating it as an equation
-- against an eta-expanded lambda forces the kernel to def-eq the TERM,
-- which drives `whnf` into `whnf_const_head`'s Rec arm with that short
-- spine. Pins the spine-length guard in `try_k_synth_iota`.
public theorem partialKRec :
    (@Eq.rec Nat 0 (fun _ _ => Nat) 1 0) = (fun _ => 1) := rfl

-- Deep-telescope outer-reference shape (the mathlib
-- `Algebra.kerTensorProductMapIdToAlgHomEquiv._proof_1` failure shape,
-- minimized): the def-eq obligations under the inner binders reference
-- ONLY the outermost binder, so in de Bruijn their loose range spans
-- the whole context and the prefix trim keeps every (unreferenced)
-- inner frame. Without rebasing, each comparison site's inner-frame
-- spelling mints a fresh memo key — measured 164x context multiplicity
-- per distinct pair on the mathlib constant. Pins `k_def_eq_rebase`:
-- both sides lower by their shared minimum loose index and the
-- unreferenced frames drop from the key.
public theorem deepRebase :
    ∀ (n : Nat) (_a _b _c _d _e _f _g _h _i _j : Nat),
      n + 0 = n :=
  fun n _ _ _ _ _ _ _ _ _ _ => Nat.add_zero n

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
         interpret := false, withProof := false }

/-- kernel check with equivalent transitive typecheck semantic.
    Reshapes an `Ix.Claim.check target none` request as a `CheckEnv`
    claim whose owned tree lists the target's transitive closure —
    every member gets typechecked, not just the target. Kernel path:
    verify_claim → run_check_env → per-leaf run_check.

    Blake3 binding is preserved end-to-end: every closure member
    reaches the kernel via `get_ci(addr)` which reads bytes from
    ch 2 and asserts blake3(bytes) == addr before returning. -/
public def kernelCheck (name : Lean.Name) (env : Lean.Environment) :
    IO AiurTestCase := do
  let ixonEnv ← loadIxonEnv name env
  let target ← lookupAddr ixonEnv name
  -- Claim.Check with transitive semantics: run_check_transitive walks the
  -- block-level ref DAG lazily. No AssumptionTree needed — Aiur
  -- memoization ensures every reachable const/block gets checked exactly
  -- once, and the FFT cost stays pure typecheck cost with no tree
  -- hash-verify overhead folded in.
  let claim := Ix.Claim.check target none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv claim {}
  pure { functionName := witness.funcName, label := s!"Kernel check {name}"
         input := witness.input, inputIOBuffer := witness.inputIOBuffer
         expectedIOBuffer := witness.inputIOBuffer
         interpret := false, withProof := false }

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none   => .mkStr acc s

/-- Exact FFT-cost pins, one per checked constant. These are equality
    assertions, not budgets: any kernel change that shifts the cost of a
    listed constant fails the suite, so a regression cannot land quietly
    and an improvement has to be acknowledged by re-pinning. -/
private def kernelCheckEntries : List (String × Nat) := [
  ("HEq",                                                        129_469_755),
  ("HEq.rec",                                                    132_909_464),
  ("Eq.rec",                                                     132_480_820),
  ("Nat",                                                        129_465_849),
  ("Nat.add",                                                    165_108_235),
  ("Nat.add_comm",                                               292_242_758),
  ("Nat.decEq",                                                  341_707_387),
  ("Nat.decLe",                                                  732_657_452),
  ("Nat.sub_le_of_le_add",                                     1_793_205_442),
  ("Nat.shiftRight_succ",                                      1_331_102_738),
  ("Trans.mk",                                                   134_730_957),
  ("Array.append_assoc",                                       8_622_692_040),
  ("Vector.append",                                            8_832_888_886),
  ("IxVMPrim.nat_add_lit",                                       205_744_014),
  ("IxVMPrim.nat_sub_lit",                                       222_287_107),
  ("IxVMPrim.nat_mul_lit",                                       197_347_035),
  ("IxVMPrim.nat_mul_big",                                       195_715_265),
  ("IxVMPrim.nat_div_lit",                                     1_300_378_131),
  ("IxVMPrim.nat_mod_lit",                                     1_325_771_748),
  ("IxVMPrim.nat_succ_lit",                                      143_978_626),
  ("IxVMPrim.nat_pred_lit",                                      165_098_809),
  ("IxVMPrim.nat_gcd_lit",                                     2_077_875_037),
  ("IxVMPrim.nat_land_lit",                                    3_392_628_936),
  ("IxVMPrim.nat_lor_lit",                                     3_395_032_820),
  ("IxVMPrim.nat_xor_lit",                                     3_414_916_988),
  ("IxVMPrim.nat_shl_lit",                                       225_066_345),
  ("IxVMPrim.nat_shr_lit",                                     1_315_383_051),
  ("IxVMPrim.nat_pow_big",                                       386_956_148),
  ("IxVMPrim.nat_beq_lit",                                       195_527_816),
  ("IxVMPrim.nat_ble_lit",                                       190_284_620),
  ("IxVMPrim.nat_cases_big",                                     164_642_476),
  ("IxVMPrim.nat_dec_le",                                        750_986_524),
  ("IxVMPrim.nat_dec_lt",                                        762_210_013),
  ("IxVMPrim.nat_dec_eq",                                        380_473_966),
  ("IxVMPrim.str_size_lit",                                    2_388_962_323),
  ("IxVMPrim.bv_to_nat_lit",                                   1_978_208_344),
  ("IxVMInd.Even",                                               199_966_660),
  ("IxVMInd.Odd",                                                199_969_276),
  ("IxVMInd.Even.rec",                                           217_279_691),
  ("IxVMInd.Odd.rec",                                            217_283_382),
  ("IxVMInd.Tree",                                               130_859_701),
  ("IxVMInd.Tree.rec",                                           139_893_499),
  ("IxVMInd.DedupM",                                             134_176_463),
  ("IxVMInd.DedupM.rec",                                         146_306_395),
  ("IxVMInd.DepthM",                                             132_569_215),
  ("IxVMInd.DepthM.rec",                                         142_704_418),
  ("String.Internal.append",                                   2_360_699_665),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_499_115_666),
  ("Lean.Syntax.rec",                                          2_415_356_521),
  ("IxVMInd.AuxTie",                                             315_174_634),
  ("IxVMInd.AuxTie.rec",                                         353_883_253),
  ("IxVMInd.HiddenIdx",                                          130_051_904),
  ("IxVMInd.HiddenIdx.rec",                                      132_547_266),
  ("IxVMInd.thmMajorUse",                                        488_842_904),
  ("IxVMInd.partialKRec",                                        149_918_369),
  ("IxVMInd.deepRebase",                                         208_438_994),
  ("String.Slice.Pattern.Model.NoPrefixForwardPatternModel.rec", 3_305_700_695),
  ("Lean.Widget.TaggedText.rec",                               2_384_606_378),
  ("Lean.Doc.Part.rec",                                        2_425_558_503),
  ("Lean.Doc.Block.rec",                                       2_582_190_779),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 132_248_321),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 135_213_795),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 134_207_465),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 134_207_465),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 134_207_465),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 132_446_659),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 142_674_702),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 142_673_915),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 134_207_465),
  ("strOfListFoldSize",                                        2_677_213_762),
  ("strOfListFoldSizeAscii",                                   2_678_143_050),
]

/-- Variant of `kernelChecks`, pinned to the baseline
    (`kernelCheckEntries`). Any kernel change that shifts the kernel FFT
    cost fails the suite and forces a manual pin bump. -/
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
    interpret := false, withProof := false }

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

/-- the kernel `Check` with `assumptions = some tree.root` covering every
    transitive dep — the cutoff walk (strict=0) stops at each frontier
    member, so the kernel ends up checking only the subject. the kernel analog
    of `claimCheckWithAsm`. -/
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

/-- the kernel CheckEnv, self-contained: owned tree = every env constant.
    Exercises the R1 strict owned-membership rule over a closure that
    covers itself (walk-reachable ⊆ owned, empty asm). -/
public def claimCheckEnvFull (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let some tree := envCanonicalTree ixonEnv
    | throw <| IO.userError "envCanonicalTree empty"
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.checkEnv tree.root none) (singletonTrees tree)
  pure (asTestCase "CheckEnv self-contained (shared smoke env)" witness)

/-- the kernel CheckEnv with a thin frontier asm: owned = {Nat.add_comm},
    asm = the direct block-level refs of its constant. Exercises the
    R1 asm-cutoff walk: the single owned leaf is checked, the walk
    stops at every frontier member (no recursion below), and strict
    membership passes because the leaf is owned. Bytes for the full
    closure stay in ch 2 — delta unfolding punches through the
    frontier, only the CHECK scope stops there. -/
public def claimCheckEnvFrontier (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let target ← lookupAddr ixonEnv ``Nat.add_comm
  let some c := ixonEnv.getConst? target
    | throw <| IO.userError "Nat.add_comm constant missing"
  let some ownedTree := Ix.AssumptionTree.canonical #[target]
    | throw <| IO.userError "owned tree build failed"
  let some asmTree := Ix.AssumptionTree.canonical c.refs
    | throw <| IO.userError "asm (frontier) tree build failed"
  let trees := (singletonTrees ownedTree).insert asmTree.root asmTree
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.checkEnv ownedTree.root (some asmTree.root)) trees
  pure (asTestCase "CheckEnv frontier-asm (Nat.add_comm)" witness)

/-- the kernel `Reveal` Defn (kind+safety) — coverage. -/
public def claimRevealDefnFields (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Defn"
    fun ci => match ci with | .defn _ => true | _ => false
  let .defn d := info
    | throw <| IO.userError "findConstWith returned non-Defn"
  let revealInfo : Ix.RevealConstantInfo :=
    .defn (some d.kind) (some d.safety) none none none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal comm revealInfo) {}
  pure (asTestCase "Claim Reveal Defn (kind+safety)" witness)

/-- the kernel `Reveal` Defn `typ` via content-hash binding — exercises the
    the kernel `expr_addr` path. -/
public def claimRevealDefnExpr (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "Defn"
    fun ci => match ci with | .defn _ => true | _ => false
  let .defn d := info
    | throw <| IO.userError "findConstWith returned non-Defn"
  let typAddr := Address.blake3 (Ixon.runPut (Ixon.putExpr d.typ))
  let revealInfo : Ix.RevealConstantInfo :=
    .defn none none none (some typAddr) none
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal comm revealInfo) {}
  pure (asTestCase "Claim Reveal Defn (typ Expr addr)" witness)

/-- the kernel `Reveal` CPrj — all projection fields. coverage. -/
public def claimRevealCPrj (ixonEnv : Ixon.Env) : IO AiurTestCase := do
  let (comm, info) ← findConstWithOrThrow ixonEnv "CPrj"
    fun ci => match ci with | .cPrj _ => true | _ => false
  let .cPrj p := info
    | throw <| IO.userError "findConstWith returned non-CPrj"
  let revealInfo : Ix.RevealConstantInfo :=
    .cPrj (some p.idx) (some p.cidx) (some p.block)
  let witness ← IO.ofExcept <| buildClaimWitness ixonEnv
    (Ix.Claim.reveal comm revealInfo) {}
  pure (asTestCase "Claim Reveal CPrj (all fields)" witness)

/-- the kernel `Contains` against a synthetic 3-leaf tree. -/
public def claimContains : IO AiurTestCase := do
  let a : Address := ⟨⟨Array.replicate 32 0x11⟩⟩
  let b : Address := ⟨⟨Array.replicate 32 0x22⟩⟩
  let c : Address := ⟨⟨Array.replicate 32 0x33⟩⟩
  let some tree := Ix.AssumptionTree.canonical #[a, b, c]
    | throw <| IO.userError "Contains tree build failed"
  let witness ← IO.ofExcept <| buildClaimWitness ({} : Ixon.Env)
    (Ix.Claim.contains tree.root b) (singletonTrees tree)
  pure (asTestCase "Claim Contains (synthetic 3-leaf)" witness)


/-! ## Shard pipeline

The one path where the WITNESS is built in Rust rather than Lean:
`shardCheckWithEnv` hands an `EnvHandle` plus an owned-address blob to
`build_shard_check_env_witness`, which walks the closure, converts
bytes, and commits the thin-frontier asm tree in parallel Rust. Every
other suite case builds its witness Lean-side, so without this the
Rust builder — including the thin-frontier convention that determines
CheckEnv claim digests — would be untested. -/

/-- Group key for shard partitioning: projection wrappers group with
    their block, everything else is its own group. Keeps a block and
    all its wrappers in one shard, so an owned set is walk-closed at
    both block and wrapper granularity. -/
private def shardGroupOf (a : Address) (ci : Ixon.ConstantInfo) : Address :=
  match ci with
  | .iPrj p | .cPrj p | .rPrj p | .dPrj p => p.block
  | _ => a

/-- Root namespace component of an Ixon name (`String.utf8ByteSize` →
    `"String"`). -/
private partial def ixNameRoot : Ix.Name → Option String
  | .str (.anonymous _) s _ => some s
  | .str p _ _ => ixNameRoot p
  | .num p _ _ => ixNameRoot p
  | .anonymous _ => none

/-- Synthetic shard over the utf8-decode theorem's closure: owned = the
    `String`/`Char` subsystem's block groups, frontier = its direct
    out-of-owned refs. Non-toy on all three axes (owned in the dozens,
    closure in the thousands, frontier in the hundreds) while staying
    inside a few B FFT.

    Runs through the Rust witness builder + native kernel via
    `shardCheckWithEnv`. Execution-only: the pinned FFT cost is the
    regression signal. -/
public def shardCheckEnvCase (env : Lean.Environment) :
    IO (Option (Aiur.EnvHandle × ByteArray)) := do
  let base : Lean.Name :=
    .str (.str .anonymous "ByteArray") "utf8DecodeChar?_utf8EncodeChar_append"
  if !env.constants.contains base then return none
  let ixonEnv ← loadIxonEnv base env
  let mut groups : Std.HashMap Address (Array Address) := {}
  let mut ownedGroups : Std.HashSet Address := {}
  for (a, lc) in ixonEnv.consts do
    if let some c := lc.get? then
      let k := shardGroupOf a c.info
      groups := groups.insert k ((groups.getD k #[]).push a)
      if let some n := ixonEnv.addrToName[a]? then
        if ixNameRoot n == some "String" || ixNameRoot n == some "Char" then
          ownedGroups := ownedGroups.insert k
  let mut owned : Array Address := #[]
  for k in ownedGroups.toArray do owned := owned ++ groups.getD k #[]
  -- Distinct from the `none` above, which means the target constant is
  -- absent from this toolchain. Reaching here means the target EXISTS but
  -- the shard partitioning selected nothing to own, i.e. the fixture
  -- stopped exercising the Rust witness builder and thin-frontier claim
  -- convention. Reporting that as a skip would leave the only test of
  -- that path permanently green while testing nothing.
  if owned.isEmpty then
    throw <| IO.userError "shardCheckEnvCase: target present but the \
      partition selected zero owned constants — fixture no longer \
      exercises the shard pipeline"
  let envBytes ← IO.ofExcept (Ixon.serEnv ixonEnv)
  let handle ← IO.ofExcept (Aiur.EnvHandle.fromBytes envBytes)
  let ownedBlob : ByteArray := owned.foldl (fun b a => b ++ a.hash) .empty
  return some (handle, ownedBlob)
