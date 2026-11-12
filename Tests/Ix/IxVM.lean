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
  ("HEq", 185_513_071),
  ("HEq.rec", 192_334_148),
  ("Eq.rec", 190_651_310),
  ("Nat", 184_926_795),
  ("Nat.add", 240_653_120),
  ("Nat.add_comm", 420_841_441),
  ("Nat.decEq", 494_924_519),
  ("Nat.decLe", 1_001_696_889),
  ("Nat.sub_le_of_le_add", 2_202_345_063),
  ("Nat.shiftRight_succ", 360_192_181),
  ("Trans.mk", 195_942_915),
  ("Array.append_assoc", 12_084_644_820),
  ("Vector.append", 12_344_527_197),
  ("IxVMPrim.nat_add_lit", 234_063_343),
  ("IxVMPrim.nat_sub_lit", 234_151_262),
  ("IxVMPrim.nat_mul_lit", 207_824_723),
  ("IxVMPrim.nat_mul_big", 206_435_178),
  ("IxVMPrim.nat_div_lit", 211_811_494),
  ("IxVMPrim.nat_mod_lit", 212_104_304),
  ("IxVMPrim.nat_succ_lit", 204_933_289),
  ("IxVMPrim.nat_pred_lit", 220_349_830),
  ("IxVMPrim.nat_gcd_lit", 208_484_244),
  ("IxVMPrim.nat_land_lit", 205_766_240),
  ("IxVMPrim.nat_lor_lit", 207_289_545),
  ("IxVMPrim.nat_xor_lit", 208_176_407),
  ("IxVMPrim.nat_shl_lit", 208_488_278),
  ("IxVMPrim.nat_shr_lit", 208_749_865),
  ("IxVMPrim.nat_pow_big", 990_672_748),
  ("IxVMPrim.nat_beq_lit", 208_632_629),
  ("IxVMPrim.nat_ble_lit", 209_744_391),
  ("IxVMPrim.nat_cases_big", 230_576_849),
  ("IxVMPrim.nat_dec_le", 271_653_565),
  ("IxVMPrim.nat_dec_lt", 282_388_773),
  ("IxVMPrim.nat_dec_eq", 246_437_991),
  ("IxVMPrim.str_size_lit", 3_426_675_031),
  ("IxVMPrim.bv_to_nat_lit", 2_370_080_800),
  ("IxVMInd.Even", 445_889_449),
  ("IxVMInd.Odd", 445_835_489),
  ("IxVMInd.Even.rec", 449_859_114),
  ("IxVMInd.Odd.rec", 449_957_213),
  ("IxVMInd.IdxTeleN.rec", 430_551_303),
  ("IxVMInd.IdxTeleB.rec", 430_502_994),
  ("IxVMInd.SoloA.rec", 349_829_249),
  ("IxVMInd.SoloB.rec", 349_877_127),
  ("IxVMInd.Tree", 620_048_838),
  ("IxVMInd.Tree.rec", 622_351_705),
  ("IxVMInd.DedupM", 778_701_031),
  ("IxVMInd.DedupM.rec", 782_393_575),
  ("IxVMInd.DepthM", 798_034_340),
  ("IxVMInd.DepthM.rec", 800_447_270),
  ("String.Internal.append", 2_783_272_587),
  ("Lean.Syntax.rec", 4_073_886_835),
  ("IxVMInd.AuxTie", 1_541_339_368),
  ("IxVMInd.AuxTie.rec", 1_552_072_148),
  ("IxVMInd.HiddenIdx", 186_787_633),
  ("IxVMInd.HiddenIdx.rec", 192_228_202),
  ("IxVMInd.NestParIdx.rec", 1_004_044_259),
  ("IxVMInd.NestListIdx.rec", 941_056_628),
  ("IxVMInd.NestRefl.rec", 700_616_568),
  ("IxVMInd.NestReflOpt.rec", 572_111_451),
  ("IxVMInd.Phantom", 188_187_493),
  ("IxVMInd.thmMajorUse", 658_173_758),
  ("IxVMInd.partialKRec", 210_748_496),
  ("IxVMInd.deepRebase", 272_198_263),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_167_336_328),
  ("Lean.Widget.TaggedText.rec", 4_465_291_018),
  ("Lean.Doc.Part.rec", 24_613_481_815),
  ("Lean.Doc.Block.rec", 21_689_217_807),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_440_608_101),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_452_262_671),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_452_315_189),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_452_364_037),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 773_121_118),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_282_151_643),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_289_749_003),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_289_846_921),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_289_750_216),
  ("strOfListFoldSize", 3_558_544_629),
  ("strOfListFoldSizeAscii", 3_398_863_300),
  ("IxVMPrim.lazy_ble_offset", 238_941_049),
  ("IxVMPrim.lazy_unit_cast", 412_720_050),
  ("IxVMPrim.sizeof_unit", 224_594_775),
  ("IxVMPerf.let_continuations", 519_475_144),
  ("IxVMPerf.mul_row", 420_456_246),
  ("IxVMPerf.context_tower", 817_306_775),
  ("IxVMPerf.mul_wide", 308_102_536)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 212_029_477),
  ("IxVMPrim.nat_mul_lit", 315_369_816),
  ("IxVMPrim.nat_div_lit", 2_380_332_253),
  ("IxVMPrim.nat_land_lit", 8_651_718_737)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 652_394_817),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 665_784_388),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 1_047_515_325),
  ("Tests.Ix.Kernel.EntryCaseDefs.GA.rec", 0),
  ("Tests.Ix.Kernel.EntryCaseDefs.GI.rec", 0),
  ("Tests.Ix.Kernel.EntryCaseDefs.GE.rec", 0)]

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
             accept := true, expectedFftCost := some 127_162_668_412, witness := witness }

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
    return { c with expectedFftCost := some 424_549_607_905 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
