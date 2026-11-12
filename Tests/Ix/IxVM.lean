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
  ("HEq", 184_127_353),
  ("HEq.rec", 191_185_554),
  ("Eq.rec", 189_644_445),
  ("Nat", 183_410_673),
  ("Nat.add", 244_964_434),
  ("Nat.add_comm", 434_513_499),
  ("Nat.decEq", 514_274_843),
  ("Nat.decLe", 1_051_843_922),
  ("Nat.sub_le_of_le_add", 2_292_619_469),
  ("Nat.shiftRight_succ", 379_782_520),
  ("Trans.mk", 195_208_320),
  ("Array.append_assoc", 12_483_080_093),
  ("Vector.append", 12_749_868_678),
  ("IxVMPrim.nat_add_lit", 235_325_473),
  ("IxVMPrim.nat_sub_lit", 235_449_721),
  ("IxVMPrim.nat_mul_lit", 207_197_731),
  ("IxVMPrim.nat_mul_big", 205_844_643),
  ("IxVMPrim.nat_div_lit", 211_360_200),
  ("IxVMPrim.nat_mod_lit", 211_491_358),
  ("IxVMPrim.nat_succ_lit", 204_380_991),
  ("IxVMPrim.nat_pred_lit", 222_482_078),
  ("IxVMPrim.nat_gcd_lit", 207_962_427),
  ("IxVMPrim.nat_land_lit", 205_165_062),
  ("IxVMPrim.nat_lor_lit", 206_555_345),
  ("IxVMPrim.nat_xor_lit", 207_636_777),
  ("IxVMPrim.nat_shl_lit", 207_968_738),
  ("IxVMPrim.nat_shr_lit", 208_041_890),
  ("IxVMPrim.nat_pow_big", 991_458_388),
  ("IxVMPrim.nat_beq_lit", 208_159_403),
  ("IxVMPrim.nat_ble_lit", 209_252_909),
  ("IxVMPrim.nat_cases_big", 233_179_470),
  ("IxVMPrim.nat_dec_le", 281_291_952),
  ("IxVMPrim.nat_dec_lt", 292_320_164),
  ("IxVMPrim.nat_dec_eq", 252_684_775),
  ("IxVMPrim.str_size_lit", 3_575_945_195),
  ("IxVMPrim.bv_to_nat_lit", 2_476_670_071),
  ("IxVMInd.Even", 416_029_863),
  ("IxVMInd.Odd", 416_030_982),
  ("IxVMInd.Even.rec", 419_947_633),
  ("IxVMInd.Odd.rec", 419_995_942),
  ("IxVMInd.IdxTeleN.rec", 409_207_079),
  ("IxVMInd.IdxTeleB.rec", 409_211_541),
  ("IxVMInd.SoloA.rec", 341_384_467),
  ("IxVMInd.SoloB.rec", 341_384_467),
  ("IxVMInd.Tree", 570_522_705),
  ("IxVMInd.Tree.rec", 572_726_927),
  ("IxVMInd.DedupM", 697_775_535),
  ("IxVMInd.DedupM.rec", 701_257_438),
  ("IxVMInd.DepthM", 751_292_529),
  ("IxVMInd.DepthM.rec", 753_438_030),
  ("String.Internal.append", 2_915_073_162),
  ("Lean.Syntax.rec", 4_066_024_761),
  ("IxVMInd.AuxTie", 1_424_270_399),
  ("IxVMInd.AuxTie.rec", 1_435_131_166),
  ("IxVMInd.HiddenIdx", 185_557_113),
  ("IxVMInd.HiddenIdx.rec", 191_403_491),
  ("IxVMInd.NestParIdx.rec", 943_023_234),
  ("IxVMInd.NestListIdx.rec", 866_637_572),
  ("IxVMInd.NestRefl.rec", 643_571_061),
  ("IxVMInd.NestReflOpt.rec", 539_373_365),
  ("IxVMInd.Phantom", 186_844_910),
  ("IxVMInd.thmMajorUse", 681_236_463),
  ("IxVMInd.partialKRec", 210_477_445),
  ("IxVMInd.deepRebase", 279_131_267),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_313_096_455),
  ("Lean.Widget.TaggedText.rec", 4_418_706_083),
  ("Lean.Doc.Part.rec", 21_501_095_781),
  ("Lean.Doc.Block.rec", 18_912_218_782),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_252_595_430),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_264_224_399),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_264_223_200),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_264_222_001),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 709_980_719),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_105_815_456),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_113_341_200),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_113_340_014),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_113_436_802),
  ("strOfListFoldSize", 3_707_885_243),
  ("strOfListFoldSizeAscii", 3_548_507_039),
  ("IxVMPrim.lazy_ble_offset", 240_497_467),
  ("IxVMPrim.lazy_unit_cast", 428_409_285),
  ("IxVMPrim.sizeof_unit", 224_938_416),
  ("IxVMPerf.let_continuations", 518_262_185),
  ("IxVMPerf.mul_row", 419_818_546),
  ("IxVMPerf.context_tower", 879_731_975),
  ("IxVMPerf.mul_wide", 305_705_994)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 212_272_546),
  ("IxVMPrim.nat_mul_lit", 321_625_518),
  ("IxVMPrim.nat_div_lit", 2_465_957_139),
  ("IxVMPrim.nat_land_lit", 8_892_164_811)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 599_349_349),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 605_935_383),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 912_489_772)]

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
             accept := true, expectedFftCost := some 129_734_312_981, witness := witness }

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
    return { c with expectedFftCost := some 428_653_676_197 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
