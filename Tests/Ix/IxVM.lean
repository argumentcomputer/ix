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
`Tests.Ix.IxVMFixtures` name them.

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
  ("HEq", 226_914_318),
  ("HEq.rec", 234_574_905),
  ("Eq.rec", 232_892_579),
  ("Nat", 226_664_381),
  ("Nat.add", 290_668_963),
  ("Nat.add_comm", 496_404_584),
  ("Nat.decEq", 569_796_901),
  ("Nat.decLe", 1_132_619_372),
  ("Nat.sub_le_of_le_add", 2_455_371_238),
  ("Nat.shiftRight_succ", 438_822_293),
  ("Trans.mk", 237_715_726),
  ("Array.append_assoc", 11_579_422_329),
  ("Vector.append", 11_875_522_046),
  ("IxVMPrim.nat_add_lit", 283_615_131),
  ("IxVMPrim.nat_sub_lit", 283_648_589),
  ("IxVMPrim.nat_mul_lit", 254_179_807),
  ("IxVMPrim.nat_mul_big", 252_479_333),
  ("IxVMPrim.nat_div_lit", 260_232_377),
  ("IxVMPrim.nat_mod_lit", 260_462_899),
  ("IxVMPrim.nat_succ_lit", 250_395_788),
  ("IxVMPrim.nat_pred_lit", 254_048_434),
  ("IxVMPrim.nat_gcd_lit", 254_809_307),
  ("IxVMPrim.nat_land_lit", 251_656_673),
  ("IxVMPrim.nat_lor_lit", 253_417_020),
  ("IxVMPrim.nat_xor_lit", 255_098_175),
  ("IxVMPrim.nat_shl_lit", 254_882_832),
  ("IxVMPrim.nat_shr_lit", 255_036_814),
  ("IxVMPrim.nat_pow_big", 1_044_307_597),
  ("IxVMPrim.nat_beq_lit", 255_213_058),
  ("IxVMPrim.nat_ble_lit", 256_506_025),
  ("IxVMPrim.nat_cases_big", 280_382_486),
  ("IxVMPrim.nat_dec_le", 423_965_329),
  ("IxVMPrim.nat_dec_lt", 421_432_506),
  ("IxVMPrim.nat_dec_eq", 408_519_799),
  ("IxVMPrim.str_size_lit", 3_538_293_744),
  ("IxVMPrim.bv_to_nat_lit", 2_677_377_494),
  ("IxVMInd.Even", 276_762_815),
  ("IxVMInd.Odd", 276_769_320),
  ("IxVMInd.Even.rec", 302_560_176),
  ("IxVMInd.Odd.rec", 302_561_271),
  ("IxVMInd.IdxTeleN.rec", 275_695_689),
  ("IxVMInd.IdxTeleB.rec", 275_694_607),
  ("IxVMInd.SoloA.rec", 267_907_130),
  ("IxVMInd.SoloB.rec", 267_907_130),
  ("IxVMInd.UnsafeSquash", 230_259_072),
  ("IxVMInd.Tree", 229_580_722),
  ("IxVMInd.Tree.rec", 246_720_433),
  ("IxVMInd.DedupM", 234_815_187),
  ("IxVMInd.DedupM.rec", 257_276_690),
  ("IxVMInd.DepthM", 232_322_727),
  ("IxVMInd.DepthM.rec", 250_294_669),
  ("String.Internal.append", 3_147_646_728),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_496_952_671),
  ("Lean.Syntax.rec", 3_231_174_721),
  ("IxVMInd.AuxTie", 378_904_782),
  ("IxVMInd.AuxTie.rec", 440_753_304),
  ("IxVMInd.HiddenIdx", 228_542_504),
  ("IxVMInd.HiddenIdx.rec", 234_748_625),
  ("IxVMInd.thmMajorUse", 746_414_330),
  ("IxVMInd.partialKRec", 256_973_951),
  ("IxVMInd.deepRebase", 329_968_708),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_580_126_618),
  ("Lean.Widget.TaggedText.rec", 3_189_565_574),
  ("Lean.Doc.Part.rec", 3_251_715_438),
  ("Lean.Doc.Block.rec", 3_572_084_918),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 232_599_174),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 285_531_517),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 285_533_677),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 285_534_756),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 259_564_924),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 231_582_819),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 271_942_423),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 271_943_498),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 271_943_498),
  ("strOfListFoldSize", 3_546_819_509),
  ("strOfListFoldSizeAscii", 3_544_943_408),
  ("IxVMPrim.lazy_ble_offset", 290_927_227),
  ("IxVMPrim.lazy_unit_cast", 483_008_407),
  ("IxVMPrim.sizeof_unit", 274_282_047),
  ("IxVMPerf.let_continuations", 562_644_672),
  ("IxVMPerf.mul_row", 516_461_227),
  ("IxVMPerf.context_tower", 858_636_729),
  ("IxVMPerf.mul_wide", 357_299_705)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_210_176),
  ("IxVMPrim.nat_mul_lit", 371_448_643),
  ("IxVMPrim.nat_div_lit", 2_595_519_769),
  ("IxVMPrim.nat_land_lit", 8_939_419_380)]

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
             accept := true, expectedFftCost := some 138_875_140_469, witness := witness }

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
    return { c with expectedFftCost := some 457_260_518_442 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
