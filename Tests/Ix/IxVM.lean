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
  ("HEq", 185_511_879),
  ("HEq.rec", 192_407_726),
  ("Eq.rec", 190_697_064),
  ("Nat", 184_926_150),
  ("Nat.add", 240_604_697),
  ("Nat.add_comm", 420_616_934),
  ("Nat.decEq", 494_716_975),
  ("Nat.decLe", 1_002_467_273),
  ("Nat.sub_le_of_le_add", 2_202_977_516),
  ("Nat.shiftRight_succ", 362_427_350),
  ("Trans.mk", 195_905_782),
  ("Array.append_assoc", 12_080_230_439),
  ("Vector.append", 12_339_814_820),
  ("IxVMPrim.nat_add_lit", 234_056_390),
  ("IxVMPrim.nat_sub_lit", 234_144_214),
  ("IxVMPrim.nat_mul_lit", 207_821_080),
  ("IxVMPrim.nat_mul_big", 206_433_181),
  ("IxVMPrim.nat_div_lit", 211_794_541),
  ("IxVMPrim.nat_mod_lit", 212_087_351),
  ("IxVMPrim.nat_succ_lit", 204_931_324),
  ("IxVMPrim.nat_pred_lit", 220_346_788),
  ("IxVMPrim.nat_gcd_lit", 208_460_079),
  ("IxVMPrim.nat_land_lit", 205_763_926),
  ("IxVMPrim.nat_lor_lit", 207_286_076),
  ("IxVMPrim.nat_xor_lit", 208_172_938),
  ("IxVMPrim.nat_shl_lit", 208_465_696),
  ("IxVMPrim.nat_shr_lit", 208_719_981),
  ("IxVMPrim.nat_pow_big", 989_052_103),
  ("IxVMPrim.nat_beq_lit", 208_646_487),
  ("IxVMPrim.nat_ble_lit", 209_756_541),
  ("IxVMPrim.nat_cases_big", 230_535_427),
  ("IxVMPrim.nat_dec_le", 272_783_221),
  ("IxVMPrim.nat_dec_lt", 283_408_262),
  ("IxVMPrim.nat_dec_eq", 247_252_837),
  ("IxVMPrim.str_size_lit", 3_427_258_636),
  ("IxVMPrim.bv_to_nat_lit", 2_370_770_039),
  ("IxVMInd.Even", 446_029_315),
  ("IxVMInd.Odd", 445_975_355),
  ("IxVMInd.Even.rec", 449_998_025),
  ("IxVMInd.Odd.rec", 450_096_124),
  ("IxVMInd.IdxTeleN.rec", 430_608_818),
  ("IxVMInd.IdxTeleB.rec", 430_560_510),
  ("IxVMInd.SoloA.rec", 349_877_301),
  ("IxVMInd.SoloB.rec", 349_925_179),
  ("IxVMInd.Tree", 620_397_237),
  ("IxVMInd.Tree.rec", 622_696_159),
  ("IxVMInd.DedupM", 778_732_098),
  ("IxVMInd.DedupM.rec", 782_428_740),
  ("IxVMInd.DepthM", 798_653_913),
  ("IxVMInd.DepthM.rec", 801_070_065),
  ("String.Internal.append", 2_784_121_855),
  ("Lean.Syntax.rec", 4_074_497_667),
  ("IxVMInd.AuxTie", 1_541_204_772),
  ("IxVMInd.AuxTie.rec", 1_551_937_132),
  ("IxVMInd.HiddenIdx", 186_786_826),
  ("IxVMInd.HiddenIdx.rec", 192_274_337),
  ("IxVMInd.NestParIdx.rec", 1_005_447_560),
  ("IxVMInd.NestListIdx.rec", 941_836_619),
  ("IxVMInd.NestRefl.rec", 700_949_919),
  ("IxVMInd.NestReflOpt.rec", 572_456_879),
  ("IxVMInd.Phantom", 188_186_314),
  ("IxVMInd.thmMajorUse", 658_972_446),
  ("IxVMInd.partialKRec", 210_749_542),
  ("IxVMInd.deepRebase", 272_125_631),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_168_093_831),
  ("Lean.Widget.TaggedText.rec", 4_466_920_296),
  ("Lean.Doc.Part.rec", 24_620_102_130),
  ("Lean.Doc.Block.rec", 21_692_641_584),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_440_667_868),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_452_321_475),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_452_374_019),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_452_422_893),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 773_299_514),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_282_179_134),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_289_773_212),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_289_869_968),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_289_773_212),
  ("strOfListFoldSize", 3_558_992_669),
  ("strOfListFoldSizeAscii", 3_399_492_804),
  ("IxVMPrim.lazy_ble_offset", 238_932_795),
  ("IxVMPrim.lazy_unit_cast", 413_113_929),
  ("IxVMPrim.sizeof_unit", 224_601_023),
  ("IxVMPerf.let_continuations", 517_180_462),
  ("IxVMPerf.mul_row", 420_310_985),
  ("IxVMPerf.context_tower", 815_013_991),
  ("IxVMPerf.mul_wide", 306_284_556)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 212_029_670),
  ("IxVMPrim.nat_mul_lit", 315_168_856),
  ("IxVMPrim.nat_div_lit", 2_379_619_098),
  ("IxVMPrim.nat_land_lit", 8_645_233_571)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 652_724_169),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 666_123_544),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 1_048_296_043)]

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
             accept := true, expectedFftCost := some 127_039_745_689, witness := witness }

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
    return { c with expectedFftCost := some 423_961_811_871 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
