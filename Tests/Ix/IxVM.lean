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
  ("HEq", 184_189_010),
  ("HEq.rec", 191_255_032),
  ("Eq.rec", 189_584_375),
  ("Nat", 183_597_178),
  ("Nat.add", 243_473_226),
  ("Nat.add_comm", 429_852_915),
  ("Nat.decEq", 508_104_571),
  ("Nat.decLe", 1_038_418_773),
  ("Nat.sub_le_of_le_add", 2_263_720_496),
  ("Nat.shiftRight_succ", 375_589_868),
  ("Trans.mk", 195_018_123),
  ("Array.append_assoc", 12_353_263_353),
  ("Vector.append", 12_617_724_439),
  ("IxVMPrim.nat_add_lit", 234_150_064),
  ("IxVMPrim.nat_sub_lit", 234_199_368),
  ("IxVMPrim.nat_mul_lit", 207_112_462),
  ("IxVMPrim.nat_mul_big", 205_724_816),
  ("IxVMPrim.nat_div_lit", 211_044_100),
  ("IxVMPrim.nat_mod_lit", 211_347_728),
  ("IxVMPrim.nat_succ_lit", 204_312_933),
  ("IxVMPrim.nat_pred_lit", 222_041_343),
  ("IxVMPrim.nat_gcd_lit", 207_742_760),
  ("IxVMPrim.nat_land_lit", 205_164_715),
  ("IxVMPrim.nat_lor_lit", 206_319_679),
  ("IxVMPrim.nat_xor_lit", 207_500_103),
  ("IxVMPrim.nat_shl_lit", 207_726_462),
  ("IxVMPrim.nat_shr_lit", 207_966_910),
  ("IxVMPrim.nat_pow_big", 1_005_357_156),
  ("IxVMPrim.nat_beq_lit", 207_966_530),
  ("IxVMPrim.nat_ble_lit", 209_158_556),
  ("IxVMPrim.nat_cases_big", 232_834_424),
  ("IxVMPrim.nat_dec_le", 279_416_195),
  ("IxVMPrim.nat_dec_lt", 290_264_770),
  ("IxVMPrim.nat_dec_eq", 251_579_980),
  ("IxVMPrim.str_size_lit", 3_526_362_037),
  ("IxVMPrim.bv_to_nat_lit", 2_442_638_512),
  ("IxVMInd.Even", 409_647_489),
  ("IxVMInd.Odd", 409_741_423),
  ("IxVMInd.Even.rec", 413_445_362),
  ("IxVMInd.Odd.rec", 413_444_246),
  ("IxVMInd.IdxTeleN.rec", 403_875_349),
  ("IxVMInd.IdxTeleB.rec", 403_921_317),
  ("IxVMInd.SoloA.rec", 337_688_657),
  ("IxVMInd.SoloB.rec", 337_782_984),
  ("IxVMInd.Tree", 565_888_619),
  ("IxVMInd.Tree.rec", 568_093_317),
  ("IxVMInd.DedupM", 688_723_872),
  ("IxVMInd.DedupM.rec", 692_242_300),
  ("IxVMInd.DepthM", 744_610_041),
  ("IxVMInd.DepthM.rec", 746_760_434),
  ("String.Internal.append", 2_873_090_370),
  ("Lean.Syntax.rec", 4_012_489_132),
  ("IxVMInd.AuxTie", 1_398_001_348),
  ("IxVMInd.AuxTie.rec", 1_408_649_510),
  ("IxVMInd.HiddenIdx", 185_478_182),
  ("IxVMInd.HiddenIdx.rec", 191_282_403),
  ("IxVMInd.NestParIdx.rec", 937_788_600),
  ("IxVMInd.NestListIdx.rec", 860_222_567),
  ("IxVMInd.NestRefl.rec", 636_426_963),
  ("IxVMInd.NestReflOpt.rec", 534_728_719),
  ("IxVMInd.Phantom", 187_114_012),
  ("IxVMInd.thmMajorUse", 673_796_383),
  ("IxVMInd.partialKRec", 210_390_323),
  ("IxVMInd.deepRebase", 275_822_212),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_264_073_754),
  ("Lean.Widget.TaggedText.rec", 4_378_872_080),
  ("Lean.Doc.Part.rec", 21_392_191_041),
  ("Lean.Doc.Block.rec", 18_811_499_320),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_228_095_452),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_239_397_896),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_239_455_094),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_239_452_703),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 700_348_798),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_091_227_590),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_098_857_124),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_098_761_385),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_098_812_215),
  ("strOfListFoldSize", 3_658_668_128),
  ("strOfListFoldSizeAscii", 3_498_681_338),
  ("IxVMPrim.lazy_ble_offset", 239_555_004),
  ("IxVMPrim.lazy_unit_cast", 423_900_390),
  ("IxVMPrim.sizeof_unit", 224_919_029),
  ("IxVMPerf.let_continuations", 520_732_734),
  ("IxVMPerf.mul_row", 457_036_989),
  ("IxVMPerf.context_tower", 886_719_335),
  ("IxVMPerf.mul_wide", 309_343_247)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_992_842),
  ("IxVMPrim.nat_mul_lit", 320_031_460),
  ("IxVMPrim.nat_div_lit", 2_441_610_558),
  ("IxVMPrim.nat_land_lit", 8_842_295_232)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 592_194_089),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 597_920_974),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 904_976_761)]

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
             accept := true, expectedFftCost := some 129_059_334_688, witness := witness }

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
    return { c with expectedFftCost := some 427_744_204_861 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
