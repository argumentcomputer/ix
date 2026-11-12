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
  ("HEq", 185_523_160),
  ("HEq.rec", 192_379_945),
  ("Eq.rec", 190_667_883),
  ("Nat", 184_927_848),
  ("Nat.add", 240_664_568),
  ("Nat.add_comm", 420_986_783),
  ("Nat.decEq", 494_995_187),
  ("Nat.decLe", 1_001_252_636),
  ("Nat.sub_le_of_le_add", 2_202_139_601),
  ("Nat.shiftRight_succ", 360_304_142),
  ("Trans.mk", 195_989_412),
  ("Array.append_assoc", 12_096_674_648),
  ("Vector.append", 12_356_676_177),
  ("IxVMPrim.nat_add_lit", 234_146_158),
  ("IxVMPrim.nat_sub_lit", 234_233_611),
  ("IxVMPrim.nat_mul_lit", 207_852_676),
  ("IxVMPrim.nat_mul_big", 206_462_639),
  ("IxVMPrim.nat_div_lit", 211_836_106),
  ("IxVMPrim.nat_mod_lit", 212_128_916),
  ("IxVMPrim.nat_succ_lit", 204_959_983),
  ("IxVMPrim.nat_pred_lit", 220_379_647),
  ("IxVMPrim.nat_gcd_lit", 208_506_454),
  ("IxVMPrim.nat_land_lit", 205_794_127),
  ("IxVMPrim.nat_lor_lit", 207_318_893),
  ("IxVMPrim.nat_xor_lit", 208_205_756),
  ("IxVMPrim.nat_shl_lit", 208_509_861),
  ("IxVMPrim.nat_shr_lit", 208_770_627),
  ("IxVMPrim.nat_pow_big", 990_700_973),
  ("IxVMPrim.nat_beq_lit", 208_665_950),
  ("IxVMPrim.nat_ble_lit", 209_779_272),
  ("IxVMPrim.nat_cases_big", 230_615_411),
  ("IxVMPrim.nat_dec_le", 271_720_065),
  ("IxVMPrim.nat_dec_lt", 282_458_456),
  ("IxVMPrim.nat_dec_eq", 246_496_415),
  ("IxVMPrim.str_size_lit", 3_426_508_481),
  ("IxVMPrim.bv_to_nat_lit", 2_369_971_635),
  ("IxVMInd.Even", 450_061_512),
  ("IxVMInd.Odd", 450_058_129),
  ("IxVMInd.Even.rec", 451_883_256),
  ("IxVMInd.Odd.rec", 451_982_482),
  ("IxVMInd.IdxTeleN.rec", 433_141_180),
  ("IxVMInd.IdxTeleB.rec", 433_096_236),
  ("IxVMInd.SoloA.rec", 352_439_491),
  ("IxVMInd.SoloB.rec", 352_488_467),
  ("IxVMInd.Tree", 627_209_167),
  ("IxVMInd.Tree.rec", 628_254_048),
  ("IxVMInd.DedupM", 789_291_922),
  ("IxVMInd.DedupM.rec", 790_472_400),
  ("IxVMInd.DepthM", 806_176_770),
  ("IxVMInd.DepthM.rec", 807_329_112),
  ("String.Internal.append", 2_783_113_450),
  ("Lean.Syntax.rec", 4_077_518_079),
  ("IxVMInd.AuxTie", 1_563_098_312),
  ("IxVMInd.AuxTie.rec", 1_565_151_413),
  ("IxVMInd.HiddenIdx", 186_797_154),
  ("IxVMInd.HiddenIdx.rec", 192_217_796),
  ("IxVMInd.NestParIdx.rec", 1_010_597_235),
  ("IxVMInd.NestListIdx.rec", 947_334_880),
  ("IxVMInd.NestRefl.rec", 706_629_946),
  ("IxVMInd.NestReflOpt.rec", 578_112_805),
  ("IxVMInd.Phantom", 188_191_357),
  ("IxVMInd.thmMajorUse", 657_604_980),
  ("IxVMInd.partialKRec", 210_776_177),
  ("IxVMInd.deepRebase", 272_290_524),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_167_231_726),
  ("Lean.Widget.TaggedText.rec", 4_470_191_355),
  ("Lean.Doc.Part.rec", 24_767_264_182),
  ("Lean.Doc.Block.rec", 21_755_344_587),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_461_973_599),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_464_449_165),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_464_501_683),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_464_551_755),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 780_584_403),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_298_093_462),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_299_789_713),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_299_886_418),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_299_789_713),
  ("strOfListFoldSize", 3_558_372_288),
  ("strOfListFoldSizeAscii", 3_398_693_471),
  ("IxVMPrim.lazy_ble_offset", 239_030_119),
  ("IxVMPrim.lazy_unit_cast", 412_811_267),
  ("IxVMPrim.sizeof_unit", 224_643_221),
  ("IxVMPerf.let_continuations", 519_475_537),
  ("IxVMPerf.mul_row", 420_177_063),
  ("IxVMPerf.context_tower", 817_326_634),
  ("IxVMPerf.mul_wide", 307_455_991)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_841_983),
  ("IxVMPrim.nat_mul_lit", 315_214_356),
  ("IxVMPrim.nat_div_lit", 2_380_287_044),
  ("IxVMPrim.nat_land_lit", 8_651_793_637)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 658_598_897),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 671_642_713),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 1_054_480_975),
  ("Tests.Ix.Kernel.EntryCaseDefs.GA.rec", 650_145_744),
  ("Tests.Ix.Kernel.EntryCaseDefs.GI.rec", 717_076_254),
  ("Tests.Ix.Kernel.EntryCaseDefs.GE.rec", 334_744_323)]

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
             accept := true, expectedFftCost := some 127_174_710_411, witness := witness }

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
    return { c with expectedFftCost := some 424_586_150_523 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
