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
  ("HEq", 194_779_266),
  ("HEq.rec", 201_915_203),
  ("Eq.rec", 200_250_032),
  ("Nat", 194_542_218),
  ("Nat.add", 252_596_018),
  ("Nat.add_comm", 440_884_704),
  ("Nat.decEq", 511_786_387),
  ("Nat.decLe", 1_032_950_531),
  ("Nat.sub_le_of_le_add", 2_264_010_837),
  ("Nat.shiftRight_succ", 382_727_399),
  ("Trans.mk", 205_221_495),
  ("Array.append_assoc", 12_260_768_814),
  ("Vector.append", 12_537_664_610),
  ("IxVMPrim.nat_add_lit", 245_610_052),
  ("IxVMPrim.nat_sub_lit", 245_645_441),
  ("IxVMPrim.nat_mul_lit", 218_706_516),
  ("IxVMPrim.nat_mul_big", 217_168_958),
  ("IxVMPrim.nat_div_lit", 223_755_640),
  ("IxVMPrim.nat_mod_lit", 223_953_529),
  ("IxVMPrim.nat_succ_lit", 215_455_761),
  ("IxVMPrim.nat_pred_lit", 218_434_107),
  ("IxVMPrim.nat_gcd_lit", 219_337_507),
  ("IxVMPrim.nat_land_lit", 216_442_542),
  ("IxVMPrim.nat_lor_lit", 218_020_074),
  ("IxVMPrim.nat_xor_lit", 219_374_948),
  ("IxVMPrim.nat_shl_lit", 219_410_274),
  ("IxVMPrim.nat_shr_lit", 219_561_656),
  ("IxVMPrim.nat_pow_big", 1_002_888_014),
  ("IxVMPrim.nat_beq_lit", 219_528_820),
  ("IxVMPrim.nat_ble_lit", 220_686_978),
  ("IxVMPrim.nat_cases_big", 242_353_867),
  ("IxVMPrim.nat_dec_le", 373_361_653),
  ("IxVMPrim.nat_dec_lt", 371_532_965),
  ("IxVMPrim.nat_dec_eq", 359_302_076),
  ("IxVMPrim.str_size_lit", 3_253_527_625),
  ("IxVMPrim.bv_to_nat_lit", 2_466_702_806),
  ("IxVMInd.Even", 473_953_711),
  ("IxVMInd.Odd", 473_954_882),
  ("IxVMInd.Even.rec", 478_066_843),
  ("IxVMInd.Odd.rec", 478_066_843),
  ("IxVMInd.IdxTeleN.rec", 457_278_358),
  ("IxVMInd.IdxTeleB.rec", 457_280_693),
  ("IxVMInd.SoloA.rec", 370_809_680),
  ("IxVMInd.SoloB.rec", 370_809_680),
  ("IxVMInd.Tree", 634_796_670),
  ("IxVMInd.Tree.rec", 637_078_875),
  ("IxVMInd.DedupM", 799_088_582),
  ("IxVMInd.DedupM.rec", 802_707_489),
  ("IxVMInd.DepthM", 797_347_856),
  ("IxVMInd.DepthM.rec", 799_704_259),
  ("String.Internal.append", 2_898_164_143),
  ("Lean.Syntax.rec", 4_207_909_959),
  ("IxVMInd.AuxTie", 1_562_846_263),
  ("IxVMInd.AuxTie.rec", 1_573_614_679),
  ("IxVMInd.HiddenIdx", 196_205_186),
  ("IxVMInd.HiddenIdx.rec", 201_904_706),
  ("IxVMInd.NestParIdx.rec", 985_026_645),
  ("IxVMInd.NestListIdx.rec", 936_159_262),
  ("IxVMInd.NestRefl.rec", 702_438_020),
  ("IxVMInd.NestReflOpt.rec", 590_538_629),
  ("IxVMInd.thmMajorUse", 677_404_631),
  ("IxVMInd.partialKRec", 221_567_484),
  ("IxVMInd.deepRebase", 286_626_208),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_292_370_175),
  ("Lean.Widget.TaggedText.rec", 4_508_371_186),
  ("Lean.Doc.Part.rec", 23_491_821_846),
  ("Lean.Doc.Block.rec", 20_711_820_590),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_444_431_471),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_456_103_236),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_456_104_498),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_456_104_498),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 794_282_473),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_286_727_680),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_294_213_122),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_294_213_122),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_294_213_122),
  ("strOfListFoldSize", 3_261_159_076),
  ("strOfListFoldSizeAscii", 3_259_242_054),
  ("IxVMPrim.lazy_ble_offset", 251_550_452),
  ("IxVMPrim.lazy_unit_cast", 426_320_550),
  ("IxVMPrim.sizeof_unit", 236_475_970),
  ("IxVMPerf.let_continuations", 527_024_681),
  ("IxVMPerf.mul_row", 456_266_261),
  ("IxVMPerf.context_tower", 794_659_452),
  ("IxVMPerf.mul_wide", 318_640_347)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 222_778_759),
  ("IxVMPrim.nat_mul_lit", 328_365_480),
  ("IxVMPrim.nat_div_lit", 2_416_563_653),
  ("IxVMPrim.nat_land_lit", 8_450_979_543)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 670_595_578),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 683_242_967),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 0)]

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
             accept := true, expectedFftCost := some 132_565_267_736, witness := witness }

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
    return { c with expectedFftCost := some 440_827_497_654 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
