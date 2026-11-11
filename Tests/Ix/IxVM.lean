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
  ("HEq", 232_959_388),
  ("HEq.rec", 240_654_121),
  ("Eq.rec", 238_941_624),
  ("Nat", 232_374_026),
  ("Nat.add", 296_854_996),
  ("Nat.add_comm", 506_124_774),
  ("Nat.decEq", 583_655_859),
  ("Nat.decLe", 1_185_663_147),
  ("Nat.sub_le_of_le_add", 2_583_837_798),
  ("Nat.shiftRight_succ", 447_230_073),
  ("Trans.mk", 244_115_852),
  ("Array.append_assoc", 19_935_185_275),
  ("Vector.append", 20_244_763_523),
  ("IxVMPrim.nat_add_lit", 290_222_687),
  ("IxVMPrim.nat_sub_lit", 290_305_388),
  ("IxVMPrim.nat_mul_lit", 260_445_927),
  ("IxVMPrim.nat_mul_big", 258_735_820),
  ("IxVMPrim.nat_div_lit", 266_419_821),
  ("IxVMPrim.nat_mod_lit", 266_684_583),
  ("IxVMPrim.nat_succ_lit", 256_539_294),
  ("IxVMPrim.nat_pred_lit", 260_300_039),
  ("IxVMPrim.nat_gcd_lit", 261_101_830),
  ("IxVMPrim.nat_land_lit", 257_866_529),
  ("IxVMPrim.nat_lor_lit", 259_720_908),
  ("IxVMPrim.nat_xor_lit", 261_311_506),
  ("IxVMPrim.nat_shl_lit", 261_137_774),
  ("IxVMPrim.nat_shr_lit", 261_372_148),
  ("IxVMPrim.nat_pow_big", 1_040_655_995),
  ("IxVMPrim.nat_beq_lit", 261_572_360),
  ("IxVMPrim.nat_ble_lit", 262_807_867),
  ("IxVMPrim.nat_cases_big", 286_814_807),
  ("IxVMPrim.nat_dec_le", 431_104_366),
  ("IxVMPrim.nat_dec_lt", 428_138_431),
  ("IxVMPrim.nat_dec_eq", 415_768_464),
  ("IxVMPrim.str_size_lit", 3_647_986_587),
  ("IxVMPrim.bv_to_nat_lit", 2_782_333_661),
  ("IxVMInd.Even", 551_027_925),
  ("IxVMInd.Odd", 550_970_578),
  ("IxVMInd.Even.rec", 555_015_290),
  ("IxVMInd.Odd.rec", 555_118_547),
  ("IxVMInd.IdxTeleN.rec", 531_129_016),
  ("IxVMInd.IdxTeleB.rec", 531_076_378),
  ("IxVMInd.SoloA.rec", 433_988_773),
  ("IxVMInd.SoloB.rec", 434_036_390),
  ("IxVMInd.Tree", 696_932_817),
  ("IxVMInd.Tree.rec", 699_219_816),
  ("IxVMInd.DedupM", 873_923_931),
  ("IxVMInd.DedupM.rec", 877_596_356),
  ("IxVMInd.DepthM", 854_784_955),
  ("IxVMInd.DepthM.rec", 857_196_045),
  ("String.Internal.append", 3_256_346_162),
  ("Lean.Syntax.rec", 4_623_599_823),
  ("IxVMInd.AuxTie", 1_676_512_621),
  ("IxVMInd.AuxTie.rec", 1_687_152_766),
  ("IxVMInd.HiddenIdx", 234_606_627),
  ("IxVMInd.HiddenIdx.rec", 240_875_355),
  ("IxVMInd.thmMajorUse", 782_709_683),
  ("IxVMInd.partialKRec", 263_095_532),
  ("IxVMInd.deepRebase", 336_747_355),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_690_998_666),
  ("Lean.Widget.TaggedText.rec", 4_897_057_416),
  ("Lean.Doc.Part.rec", 24_182_913_911),
  ("Lean.Doc.Block.rec", 21_380_144_867),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_551_168_274),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_562_752_359),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_562_806_361),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_562_854_537),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 872_125_588),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_380_739_106),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_388_276_491),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_388_378_245),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_388_278_997),
  ("strOfListFoldSize", 3_656_620_820),
  ("strOfListFoldSizeAscii", 3_654_720_122),
  ("IxVMPrim.lazy_ble_offset", 297_681_985),
  ("IxVMPrim.lazy_unit_cast", 491_470_265),
  ("IxVMPrim.sizeof_unit", 280_749_966),
  ("IxVMPerf.let_continuations", 293_578_656),
  ("IxVMPerf.mul_row", 524_426_377),
  ("IxVMPerf.context_tower", 781_916_080),
  ("IxVMPerf.mul_wide", 364_724_402)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 264_509_885),
  ("IxVMPrim.nat_mul_lit", 377_423_799),
  ("IxVMPrim.nat_div_lit", 2_725_060_283),
  ("IxVMPrim.nat_land_lit", 10_115_661_453)]

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
             accept := true, expectedFftCost := some 197_282_084_218, witness := witness }

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
    return { c with expectedFftCost := some 1_070_159_487_520 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
