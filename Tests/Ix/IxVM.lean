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
  ("HEq", 185_523_192),
  ("HEq.rec", 192_539_057),
  ("Eq.rec", 190_791_767),
  ("Nat", 184_927_890),
  ("Nat.add", 240_817_746),
  ("Nat.add_comm", 421_193_656),
  ("Nat.decEq", 495_348_588),
  ("Nat.decLe", 1_003_551_154),
  ("Nat.sub_le_of_le_add", 2_205_118_630),
  ("Nat.shiftRight_succ", 358_009_031),
  ("Trans.mk", 196_007_555),
  ("Array.append_assoc", 12_099_632_689),
  ("Vector.append", 12_359_787_967),
  ("IxVMPrim.nat_add_lit", 234_005_453),
  ("IxVMPrim.nat_sub_lit", 234_092_952),
  ("IxVMPrim.nat_mul_lit", 207_814_586),
  ("IxVMPrim.nat_mul_big", 206_423_748),
  ("IxVMPrim.nat_div_lit", 211_794_350),
  ("IxVMPrim.nat_mod_lit", 212_087_155),
  ("IxVMPrim.nat_succ_lit", 204_921_158),
  ("IxVMPrim.nat_pred_lit", 220_532_799),
  ("IxVMPrim.nat_gcd_lit", 208_463_986),
  ("IxVMPrim.nat_land_lit", 205_755_320),
  ("IxVMPrim.nat_lor_lit", 207_280_745),
  ("IxVMPrim.nat_xor_lit", 208_167_608),
  ("IxVMPrim.nat_shl_lit", 208_467_680),
  ("IxVMPrim.nat_shr_lit", 208_727_510),
  ("IxVMPrim.nat_pow_big", 990_349_631),
  ("IxVMPrim.nat_beq_lit", 208_625_675),
  ("IxVMPrim.nat_ble_lit", 209_739_517),
  ("IxVMPrim.nat_cases_big", 230_702_118),
  ("IxVMPrim.nat_dec_le", 272_009_571),
  ("IxVMPrim.nat_dec_lt", 282_663_299),
  ("IxVMPrim.nat_dec_eq", 246_741_497),
  ("IxVMPrim.str_size_lit", 3_428_053_421),
  ("IxVMPrim.bv_to_nat_lit", 2_371_058_160),
  ("IxVMInd.Even", 451_531_986),
  ("IxVMInd.Odd", 451_530_858),
  ("IxVMInd.Even.rec", 453_353_691),
  ("IxVMInd.Odd.rec", 453_451_789),
  ("IxVMInd.IdxTeleN.rec", 434_615_029),
  ("IxVMInd.IdxTeleB.rec", 434_570_085),
  ("IxVMInd.SoloA.rec", 353_672_297),
  ("IxVMInd.SoloB.rec", 353_721_273),
  ("IxVMInd.Tree", 628_243_098),
  ("IxVMInd.Tree.rec", 629_287_498),
  ("IxVMInd.DedupM", 790_656_605),
  ("IxVMInd.DedupM.rec", 791_835_915),
  ("IxVMInd.DepthM", 807_321_078),
  ("IxVMInd.DepthM.rec", 808_472_348),
  ("String.Internal.append", 2_784_579_738),
  ("Lean.Syntax.rec", 4_081_280_654),
  ("IxVMInd.AuxTie", 1_565_999_646),
  ("IxVMInd.AuxTie.rec", 1_568_049_861),
  ("IxVMInd.HiddenIdx", 186_797_060),
  ("IxVMInd.HiddenIdx.rec", 192_347_796),
  ("IxVMInd.NestParIdx.rec", 1_010_434_017),
  ("IxVMInd.NestListIdx.rec", 947_426_259),
  ("IxVMInd.NestRefl.rec", 707_939_495),
  ("IxVMInd.NestReflOpt.rec", 579_439_139),
  ("IxVMInd.Phantom", 188_191_160),
  ("IxVMInd.thmMajorUse", 659_614_370),
  ("IxVMInd.partialKRec", 210_807_393),
  ("IxVMInd.deepRebase", 272_299_259),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_169_488_259),
  ("Lean.Widget.TaggedText.rec", 4_467_827_396),
  ("Lean.Doc.Part.rec", 24_715_231_052),
  ("Lean.Doc.Block.rec", 21_711_861_775),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_463_457_817),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_465_932_503),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_465_985_020),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_466_035_092),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 781_648_524),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_299_392_593),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_301_088_154),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_301_184_859),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_301_088_154),
  ("strOfListFoldSize", 3_559_932_962),
  ("strOfListFoldSizeAscii", 3_400_211_908),
  ("IxVMPrim.lazy_ble_offset", 238_870_826),
  ("IxVMPrim.lazy_unit_cast", 413_064_355),
  ("IxVMPrim.sizeof_unit", 224_660_775),
  ("IxVMPerf.let_continuations", 519_475_456),
  ("IxVMPerf.mul_row", 420_034_969),
  ("IxVMPerf.context_tower", 817_283_883),
  ("IxVMPerf.mul_wide", 307_405_631)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_979_083),
  ("IxVMPrim.nat_mul_lit", 315_295_017),
  ("IxVMPrim.nat_div_lit", 2_381_607_961),
  ("IxVMPrim.nat_land_lit", 8_650_424_472)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 659_873_979),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 672_777_211),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 1_054_860_639),
  ("Tests.Ix.Kernel.EntryCaseDefs.GA.rec", 651_201_841),
  ("Tests.Ix.Kernel.EntryCaseDefs.GI.rec", 718_318_301),
  ("Tests.Ix.Kernel.EntryCaseDefs.GE.rec", 335_261_878)]

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
             accept := true, expectedFftCost := some 127_177_973_834, witness := witness }

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
    return { c with expectedFftCost := some 424_703_501_174 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
