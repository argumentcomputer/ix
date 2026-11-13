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
  ("HEq", 184_201_502),
  ("HEq.rec", 190_937_048),
  ("Eq.rec", 189_313_453),
  ("Nat", 183_589_470),
  ("Nat.add", 243_611_258),
  ("Nat.add_comm", 430_133_445),
  ("Nat.decEq", 508_291_758),
  ("Nat.decLe", 1_034_944_554),
  ("Nat.sub_le_of_le_add", 2_259_793_730),
  ("Nat.shiftRight_succ", 370_920_524),
  ("Trans.mk", 195_094_688),
  ("Array.append_assoc", 12_340_234_577),
  ("Vector.append", 12_605_004_016),
  ("IxVMPrim.nat_add_lit", 234_004_124),
  ("IxVMPrim.nat_sub_lit", 234_053_295),
  ("IxVMPrim.nat_mul_lit", 207_095_651),
  ("IxVMPrim.nat_mul_big", 205_704_881),
  ("IxVMPrim.nat_div_lit", 211_033_042),
  ("IxVMPrim.nat_mod_lit", 211_336_666),
  ("IxVMPrim.nat_succ_lit", 204_292_232),
  ("IxVMPrim.nat_pred_lit", 222_233_988),
  ("IxVMPrim.nat_gcd_lit", 207_736_082),
  ("IxVMPrim.nat_land_lit", 205_145_397),
  ("IxVMPrim.nat_lor_lit", 206_306_942),
  ("IxVMPrim.nat_xor_lit", 207_487_337),
  ("IxVMPrim.nat_shl_lit", 207_718_983),
  ("IxVMPrim.nat_shr_lit", 207_964_239),
  ("IxVMPrim.nat_pow_big", 1_027_829_561),
  ("IxVMPrim.nat_beq_lit", 207_932_349),
  ("IxVMPrim.nat_ble_lit", 209_127_431),
  ("IxVMPrim.nat_cases_big", 232_984_982),
  ("IxVMPrim.nat_dec_le", 278_314_027),
  ("IxVMPrim.nat_dec_lt", 289_222_611),
  ("IxVMPrim.nat_dec_eq", 250_974_726),
  ("IxVMPrim.str_size_lit", 3_518_197_049),
  ("IxVMPrim.bv_to_nat_lit", 2_436_361_776),
  ("IxVMInd.Even", 408_172_322),
  ("IxVMInd.Odd", 408_166_738),
  ("IxVMInd.Even.rec", 409_868_069),
  ("IxVMInd.Odd.rec", 409_869_185),
  ("IxVMInd.IdxTeleN.rec", 399_517_496),
  ("IxVMInd.IdxTeleB.rec", 399_565_684),
  ("IxVMInd.SoloA.rec", 337_151_413),
  ("IxVMInd.SoloB.rec", 337_245_737),
  ("IxVMInd.Tree", 571_143_844),
  ("IxVMInd.Tree.rec", 572_177_406),
  ("IxVMInd.DedupM", 697_901_561),
  ("IxVMInd.DedupM.rec", 699_020_052),
  ("IxVMInd.DepthM", 750_832_824),
  ("IxVMInd.DepthM.rec", 751_819_973),
  ("String.Internal.append", 2_865_383_774),
  ("Lean.Syntax.rec", 4_007_894_817),
  ("IxVMInd.AuxTie", 1_417_525_768),
  ("IxVMInd.AuxTie.rec", 1_419_604_825),
  ("IxVMInd.HiddenIdx", 185_494_207),
  ("IxVMInd.HiddenIdx.rec", 191_029_009),
  ("IxVMInd.NestParIdx.rec", 939_107_280),
  ("IxVMInd.NestListIdx.rec", 862_918_621),
  ("IxVMInd.NestRefl.rec", 640_669_280),
  ("IxVMInd.NestReflOpt.rec", 539_557_789),
  ("IxVMInd.thmMajorUse", 670_461_361),
  ("IxVMInd.partialKRec", 210_417_491),
  ("IxVMInd.deepRebase", 275_920_317),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_254_758_574),
  ("Lean.Widget.TaggedText.rec", 4_368_600_482),
  ("Lean.Doc.Part.rec", 21_464_023_394),
  ("Lean.Doc.Block.rec", 18_812_729_610),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_246_625_652),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_248_987_964),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_249_039_163),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_249_036_771),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 705_387_729),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_104_416_628),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_106_248_725),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_106_155_406),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_106_207_397),
  ("strOfListFoldSize", 3_650_609_483),
  ("strOfListFoldSizeAscii", 3_490_491_906),
  ("IxVMPrim.lazy_ble_offset", 239_447_073),
  ("IxVMPrim.lazy_unit_cast", 422_876_401),
  ("IxVMPrim.sizeof_unit", 224_930_903),
  ("IxVMPerf.let_continuations", 524_011_163),
  ("IxVMPerf.mul_row", 456_554_426),
  ("IxVMPerf.context_tower", 889_948_443),
  ("IxVMPerf.mul_wide", 310_103_543)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_491_785),
  ("IxVMPrim.nat_mul_lit", 319_282_139),
  ("IxVMPrim.nat_div_lit", 2_435_145_643),
  ("IxVMPrim.nat_land_lit", 8_814_150_305)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 596_639_914),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 602_012_061),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 906_314_709)]

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
             accept := true, expectedFftCost := some 128_939_896_374, witness := witness }

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
    return { c with expectedFftCost := some 427_003_344_395 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
