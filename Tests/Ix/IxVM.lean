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
  ("HEq", 185_476_383),
  ("HEq.rec", 192_232_510),
  ("Eq.rec", 190_557_195),
  ("Nat", 184_923_720),
  ("Nat.add", 238_378_458),
  ("Nat.add_comm", 411_622_262),
  ("Nat.decEq", 480_175_758),
  ("Nat.decLe", 962_812_855),
  ("Nat.sub_le_of_le_add", 2_100_123_116),
  ("Nat.shiftRight_succ", 353_276_380),
  ("Trans.mk", 195_591_182),
  ("Array.append_assoc", 11_537_870_601),
  ("Vector.append", 11_792_873_763),
  ("IxVMPrim.nat_add_lit", 232_822_026),
  ("IxVMPrim.nat_sub_lit", 232_910_255),
  ("IxVMPrim.nat_mul_lit", 207_392_095),
  ("IxVMPrim.nat_mul_big", 206_008_638),
  ("IxVMPrim.nat_div_lit", 211_382_164),
  ("IxVMPrim.nat_mod_lit", 211_618_980),
  ("IxVMPrim.nat_succ_lit", 204_571_426),
  ("IxVMPrim.nat_pred_lit", 207_085_269),
  ("IxVMPrim.nat_gcd_lit", 208_067_032),
  ("IxVMPrim.nat_land_lit", 205_402_346),
  ("IxVMPrim.nat_lor_lit", 206_913_427),
  ("IxVMPrim.nat_xor_lit", 207_798_672),
  ("IxVMPrim.nat_shl_lit", 208_095_258),
  ("IxVMPrim.nat_shr_lit", 208_338_205),
  ("IxVMPrim.nat_pow_big", 987_441_642),
  ("IxVMPrim.nat_beq_lit", 208_232_386),
  ("IxVMPrim.nat_ble_lit", 209_337_522),
  ("IxVMPrim.nat_cases_big", 229_140_388),
  ("IxVMPrim.nat_dec_le", 349_592_735),
  ("IxVMPrim.nat_dec_lt", 348_489_334),
  ("IxVMPrim.nat_dec_eq", 336_315_651),
  ("IxVMPrim.str_size_lit", 3_000_961_375),
  ("IxVMPrim.bv_to_nat_lit", 2_283_279_306),
  ("IxVMInd.Even", 437_734_259),
  ("IxVMInd.Odd", 437_680_299),
  ("IxVMInd.Even.rec", 441_697_544),
  ("IxVMInd.Odd.rec", 441_796_771),
  ("IxVMInd.IdxTeleN.rec", 422_474_671),
  ("IxVMInd.IdxTeleB.rec", 422_426_362),
  ("IxVMInd.SoloA.rec", 344_449_869),
  ("IxVMInd.SoloB.rec", 344_497_747),
  ("IxVMInd.Tree", 592_250_836),
  ("IxVMInd.Tree.rec", 594_542_323),
  ("IxVMInd.DedupM", 740_837_508),
  ("IxVMInd.DedupM.rec", 744_503_539),
  ("IxVMInd.DepthM", 747_072_000),
  ("IxVMInd.DepthM.rec", 749_470_900),
  ("String.Internal.append", 2_680_718_269),
  ("Lean.Syntax.rec", 3_889_712_145),
  ("IxVMInd.AuxTie", 1_449_643_191),
  ("IxVMInd.AuxTie.rec", 1_460_296_448),
  ("IxVMInd.HiddenIdx", 186_750_140),
  ("IxVMInd.HiddenIdx.rec", 192_119_772),
  ("IxVMInd.thmMajorUse", 637_042_699),
  ("IxVMInd.partialKRec", 210_115_908),
  ("IxVMInd.deepRebase", 269_045_597),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_036_505_227),
  ("Lean.Widget.TaggedText.rec", 4_194_286_146),
  ("Lean.Doc.Part.rec", 22_187_941_173),
  ("Lean.Doc.Block.rec", 19_563_154_943),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_347_209_715),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_358_780_304),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_358_830_397),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_358_879_268),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 737_947_895),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_199_666_838),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_207_199_987),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_207_297_951),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_207_201_200),
  ("strOfListFoldSize", 3_007_676_328),
  ("strOfListFoldSizeAscii", 3_006_025_999),
  ("IxVMPrim.lazy_ble_offset", 237_607_169),
  ("IxVMPrim.lazy_unit_cast", 397_725_357),
  ("IxVMPrim.sizeof_unit", 223_888_884),
  ("IxVMPerf.let_continuations", 514_011_317),
  ("IxVMPerf.mul_row", 418_857_363),
  ("IxVMPerf.context_tower", 762_471_332),
  ("IxVMPerf.mul_wide", 304_168_112)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_510_763),
  ("IxVMPrim.nat_mul_lit", 310_462_821),
  ("IxVMPrim.nat_div_lit", 2_264_059_775),
  ("IxVMPrim.nat_land_lit", 7_995_052_434)]

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
             accept := true, expectedFftCost := some 124_218_178_223, witness := witness }

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
    return { c with expectedFftCost := some 422_044_432_397 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
