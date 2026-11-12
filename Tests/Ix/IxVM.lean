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
  ("HEq", 185_522_714),
  ("HEq.rec", 192_378_341),
  ("Eq.rec", 190_667_300),
  ("Nat", 184_927_475),
  ("Nat.add", 240_639_182),
  ("Nat.add_comm", 420_825_551),
  ("Nat.decEq", 494_853_707),
  ("Nat.decLe", 1_000_921_336),
  ("Nat.sub_le_of_le_add", 2_201_288_080),
  ("Nat.shiftRight_succ", 360_216_222),
  ("Trans.mk", 195_987_209),
  ("Array.append_assoc", 12_091_402_415),
  ("Vector.append", 12_351_220_976),
  ("IxVMPrim.nat_add_lit", 234_130_131),
  ("IxVMPrim.nat_sub_lit", 234_217_584),
  ("IxVMPrim.nat_mul_lit", 207_846_478),
  ("IxVMPrim.nat_mul_big", 206_457_218),
  ("IxVMPrim.nat_div_lit", 211_829_908),
  ("IxVMPrim.nat_mod_lit", 212_122_718),
  ("IxVMPrim.nat_succ_lit", 204_954_561),
  ("IxVMPrim.nat_pred_lit", 220_373_155),
  ("IxVMPrim.nat_gcd_lit", 208_500_255),
  ("IxVMPrim.nat_land_lit", 205_788_706),
  ("IxVMPrim.nat_lor_lit", 207_311_677),
  ("IxVMPrim.nat_xor_lit", 208_198_539),
  ("IxVMPrim.nat_shl_lit", 208_503_662),
  ("IxVMPrim.nat_shr_lit", 208_764_428),
  ("IxVMPrim.nat_pow_big", 990_677_314),
  ("IxVMPrim.nat_beq_lit", 208_660_569),
  ("IxVMPrim.nat_ble_lit", 209_772_279),
  ("IxVMPrim.nat_cases_big", 230_570_812),
  ("IxVMPrim.nat_dec_le", 271_702_017),
  ("IxVMPrim.nat_dec_lt", 282_346_153),
  ("IxVMPrim.nat_dec_eq", 246_479_434),
  ("IxVMPrim.str_size_lit", 3_424_920_478),
  ("IxVMPrim.bv_to_nat_lit", 2_368_860_893),
  ("IxVMInd.Even", 449_055_838),
  ("IxVMInd.Odd", 449_056_965),
  ("IxVMInd.Even.rec", 450_870_841),
  ("IxVMInd.Odd.rec", 450_968_938),
  ("IxVMInd.IdxTeleN.rec", 432_086_570),
  ("IxVMInd.IdxTeleB.rec", 432_039_383),
  ("IxVMInd.SoloA.rec", 351_429_668),
  ("IxVMInd.SoloB.rec", 351_481_938),
  ("IxVMInd.Tree", 622_262_628),
  ("IxVMInd.Tree.rec", 623_296_628),
  ("IxVMInd.DedupM", 783_956_266),
  ("IxVMInd.DedupM.rec", 785_121_269),
  ("IxVMInd.DepthM", 800_886_880),
  ("IxVMInd.DepthM.rec", 802_019_794),
  ("String.Internal.append", 2_781_859_371),
  ("Lean.Syntax.rec", 4_075_591_918),
  ("IxVMInd.AuxTie", 1_557_325_246),
  ("IxVMInd.AuxTie.rec", 1_559_375_782),
  ("IxVMInd.HiddenIdx", 186_796_329),
  ("IxVMInd.HiddenIdx.rec", 192_215_779),
  ("IxVMInd.NestParIdx.rec", 1_005_783_230),
  ("IxVMInd.NestListIdx.rec", 942_493_600),
  ("IxVMInd.NestRefl.rec", 701_825_449),
  ("IxVMInd.NestReflOpt.rec", 573_565_235),
  ("IxVMInd.Phantom", 188_190_451),
  ("IxVMInd.thmMajorUse", 657_330_544),
  ("IxVMInd.partialKRec", 210_765_928),
  ("IxVMInd.deepRebase", 272_268_346),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_165_790_826),
  ("Lean.Widget.TaggedText.rec", 4_468_144_387),
  ("Lean.Doc.Part.rec", 24_756_770_843),
  ("Lean.Doc.Block.rec", 21_745_986_478),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_456_213_416),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_458_669_686),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_458_723_428),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_458_773_500),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 775_438_658),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_292_426_561),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_294_111_087),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_294_205_366),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_294_108_661),
  ("strOfListFoldSize", 3_556_730_770),
  ("strOfListFoldSizeAscii", 3_397_118_980),
  ("IxVMPrim.lazy_ble_offset", 239_009_046),
  ("IxVMPrim.lazy_unit_cast", 412_738_480),
  ("IxVMPrim.sizeof_unit", 224_630_894),
  ("IxVMPerf.let_continuations", 519_475_375),
  ("IxVMPerf.mul_row", 420_170_865),
  ("IxVMPerf.context_tower", 817_324_119),
  ("IxVMPerf.mul_wide", 307_449_793)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_832_306),
  ("IxVMPrim.nat_mul_lit", 315_072_698),
  ("IxVMPrim.nat_div_lit", 2_378_456_518),
  ("IxVMPrim.nat_land_lit", 8_645_706_956)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 653_860_326),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 666_934_013),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 1_049_552_511)]

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
             accept := true, expectedFftCost := some 127_113_386_129, witness := witness }

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
    return { c with expectedFftCost := some 424_314_828_134 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
