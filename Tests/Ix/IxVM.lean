module

public import Ix.Meta
public import Tests.Ix.IxVM.Harness
public import Tests.Ix.IxVMFixtures

/-! # Kernel verdicts on compiled Lean constants

Every constant here is well-typed, and the IxVM program must accept a `Check`
claim on it: a transitive check of its closure (`run_check_transitive`, which
walks the block-level reference graph without an assumption tree). The
constants are the primitive reductions of `IxVMPrim`, the performance shapes of
`IxVMPerf`, the inductive shapes of `IxVMInd` (`Tests.Ix.IxVMFixtures`), the
compiler's mutual and auxiliary shapes (`Tests.Ix.Compile.Mutual`), the string
reductions (`Tests.Ix.Kernel.StringReduction`) and closures from `Init`.
Each pins a regression that once rejected it; the comments in
`Tests.Ix.IxVMFixtures` name them. Every one is in Lean's logic: a claim on an
unsafe or partial constant (`IxVMInd.UnsafeSquash`, an `_unsafe_rec`
companion) is refused at its seed (`ixvm-claim-safety`).

The claims assume their role binding (validator 4), as an aggregate's claims
do; `validatingCheckEntries` validate the roles their proofs use (validator
3), one per cost class, and the binding claim validates every role of the
default table once.

The FFT pins are exact rounded costs, not budgets. They use unpadded row
counts and the current backend's grouped circuit widths, quotient degrees,
and fixed-table heights. Both regressions and improvements require an
explicit pin update; no proving or witness-matrix allocation is needed.
-/

public section

namespace Tests.Ix.IxVM

open IxVM.ClaimHarness

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none => .mkStr acc s

/-- The constants whose claims assume their binding. -/
def kernelCheckEntries : List (String × Nat) := [
  ("HEq", 194_779_344),
  ("HEq.rec", 201_915_496),
  ("Eq.rec", 200_250_130),
  ("Nat", 194_542_223),
  ("Nat.add", 252_597_358),
  ("Nat.add_comm", 440_887_428),
  ("Nat.decEq", 511_790_698),
  ("Nat.decLe", 1_032_957_767),
  ("Nat.sub_le_of_le_add", 2_264_020_559),
  ("Nat.shiftRight_succ", 382_728_670),
  ("Trans.mk", 205_222_661),
  ("Array.append_assoc", 12_260_857_114),
  ("Vector.append", 12_537_755_400),
  ("IxVMPrim.nat_add_lit", 245_610_542),
  ("IxVMPrim.nat_sub_lit", 245_645_931),
  ("IxVMPrim.nat_mul_lit", 218_706_614),
  ("IxVMPrim.nat_mul_big", 217_169_057),
  ("IxVMPrim.nat_div_lit", 223_755_738),
  ("IxVMPrim.nat_mod_lit", 223_953_627),
  ("IxVMPrim.nat_succ_lit", 215_455_859),
  ("IxVMPrim.nat_pred_lit", 218_434_205),
  ("IxVMPrim.nat_gcd_lit", 219_337_605),
  ("IxVMPrim.nat_land_lit", 216_442_640),
  ("IxVMPrim.nat_lor_lit", 218_020_172),
  ("IxVMPrim.nat_xor_lit", 219_375_046),
  ("IxVMPrim.nat_shl_lit", 219_410_372),
  ("IxVMPrim.nat_shr_lit", 219_561_754),
  ("IxVMPrim.nat_pow_big", 1_002_888_846),
  ("IxVMPrim.nat_beq_lit", 219_528_918),
  ("IxVMPrim.nat_ble_lit", 220_687_076),
  ("IxVMPrim.nat_cases_big", 242_354_187),
  ("IxVMPrim.nat_dec_le", 373_363_064),
  ("IxVMPrim.nat_dec_lt", 371_534_376),
  ("IxVMPrim.nat_dec_eq", 359_303_416),
  ("IxVMPrim.str_size_lit", 3_253_549_519),
  ("IxVMPrim.bv_to_nat_lit", 2_466_719_339),
  ("IxVMInd.Even", 473_955_016),
  ("IxVMInd.Odd", 473_956_187),
  ("IxVMInd.Even.rec", 478_068_148),
  ("IxVMInd.Odd.rec", 478_068_148),
  ("IxVMInd.IdxTeleN.rec", 457_279_423),
  ("IxVMInd.IdxTeleB.rec", 457_281_757),
  ("IxVMInd.SoloA.rec", 370_810_610),
  ("IxVMInd.SoloB.rec", 370_810_610),
  ("IxVMInd.Tree", 634_805_092),
  ("IxVMInd.Tree.rec", 637_087_296),
  ("IxVMInd.DedupM", 799_097_466),
  ("IxVMInd.DedupM.rec", 802_716_373),
  ("IxVMInd.DepthM", 797_356_231),
  ("IxVMInd.DepthM.rec", 799_712_634),
  ("String.Internal.append", 2_898_184_951),
  ("Lean.Syntax.rec", 4_207_949_534),
  ("IxVMInd.AuxTie", 1_562_863_652),
  ("IxVMInd.AuxTie.rec", 1_573_632_068),
  ("IxVMInd.HiddenIdx", 196_205_191),
  ("IxVMInd.HiddenIdx.rec", 201_904_783),
  ("IxVMInd.NestParIdx.rec", 985_037_692),
  ("IxVMInd.NestListIdx.rec", 936_170_023),
  ("IxVMInd.NestRefl.rec", 702_447_182),
  ("IxVMInd.NestReflOpt.rec", 590_545_282),
  ("IxVMInd.Phantom", 197_684_958),
  ("IxVMInd.thmMajorUse", 677_407_953),
  ("IxVMInd.partialKRec", 221_567_725),
  ("IxVMInd.deepRebase", 286_626_819),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_292_392_278),
  ("Lean.Widget.TaggedText.rec", 4_508_417_888),
  ("Lean.Doc.Part.rec", 23_492_060_693),
  ("Lean.Doc.Block.rec", 20_712_017_718),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_444_450_739),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_456_122_504),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_456_123_766),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_456_123_766),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 794_293_092),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_286_745_777),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_294_231_219),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_294_231_219),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_294_231_219),
  ("strOfListFoldSize", 3_261_180_971),
  ("strOfListFoldSizeAscii", 3_259_263_949),
  ("IxVMPrim.lazy_ble_offset", 251_550_943),
  ("IxVMPrim.lazy_unit_cast", 426_322_470),
  ("IxVMPrim.sizeof_unit", 236_476_210),
  ("IxVMPerf.let_continuations", 527_024_681),
  ("IxVMPerf.mul_row", 456_266_360),
  ("IxVMPerf.context_tower", 794_659_551),
  ("IxVMPerf.mul_wide", 318_640_446)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 222_779_000),
  ("IxVMPrim.nat_mul_lit", 328_368_680),
  ("IxVMPrim.nat_div_lit", 2_416_591_500),
  ("IxVMPrim.nat_land_lit", 8_451_110_367)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 670_603_358),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 683_251_342),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 1_059_422_895)]

/-- A `Check` claim on `name` over `ixonEnv`. -/
def kernelCheckCase (ixonEnv : Ixon.Env) (name : Lean.Name) (assumeBinding : Bool) :
    Builder := fun _ => do
  let some target := ixonEnv.getAddr? (Ix.Name.fromLeanName name)
    | throw s!"{name} is not in the Ixon environment"
  let ctx ← Ix.ClaimContext.ofEnv ixonEnv assumeBinding
  let label := if assumeBinding then s!"check {name}"
    else s!"check {name}, validating its binding"
  Case.ofClaim label ixonEnv (.check ctx target none)

/-! ## Shard pipeline

`ix prove` checks a large environment in shards: `CheckEnv` claims over owned
block groups whose assumptions are the thin frontier of references leaving the
group (`buildShardCheckEnvWitness`, the witness `Ix.Shard.Check` builds). The
shard here is the `String`/`Char` subsystem of the closure of
`ByteArray.utf8DecodeChar?_utf8EncodeChar_append`: owned constants in the
dozens, a closure in the thousands, a frontier in the hundreds. -/

/-- Group key for shard partitioning: projection wrappers group with their
block, everything else is its own group, so an owned set is walk-closed at
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

/-- The shard case. The target missing from the environment fails rather than
skips, so that a toolchain bump that renames it cannot turn the case into a
pass; so does a partition that selects nothing to own. -/
def shardCase (env : Lean.Environment) : IO Builder := do
  let base : Lean.Name :=
    .str (.str .anonymous "ByteArray") "utf8DecodeChar?_utf8EncodeChar_append"
  unless env.constants.contains base do
    throw (IO.userError s!"{base} is not in the environment")
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
  if owned.isEmpty then
    throw (IO.userError "the shard partition selected no owned constants")
  return fun _ => do
    let (_, witness) ← buildShardCheckEnvWitness ixonEnv owned
    return { label := s!"shard CheckEnv of {owned.size} String/Char constants of {base}'s closure",
             accept := true, expectedFftCost := some 124_218_178_223, witness := witness }

/-- The verdict suite: every listed constant accepted, the binding claim of the
default table, and a shard of the shard pipeline. A listed constant missing
from the environment (a toolchain bump that renamed it) is a failure, not a
skip. -/
def kernelChecks (env : Lean.Environment) : IO UInt32 := do
  let names := (kernelCheckEntries ++ validatingCheckEntries).map (nameOfString ∘ Prod.fst)
  let missing := names.filter (!env.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-kernel-checks] not in the environment: {missing}"
    return 1
  let started ← IO.monoMsNow
  let ixonEnv ← loadSharedIxonEnv names.toArray env
  IO.println s!"[ixvm-kernel-checks] compiled the closures in {(← IO.monoMsNow) - started} ms"
  let assumed := kernelCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase ixonEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  let validating := validatingCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase ixonEnv (nameOfString n) false u
    return { c with expectedFftCost := some cost }
  let binding : Builder := fun _ => do
    let ctx ← Ix.ClaimContext.ofEnv ixonEnv
    let c ← Case.ofClaim "binding claim for the default table" ixonEnv (.binding ctx.spec ctx.binding)
    return { c with expectedFftCost := some 422_044_432_397 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
