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
  ("HEq", 199_307_558),
  ("HEq.rec", 206_605_013),
  ("Eq.rec", 204_943_687),
  ("Nat", 199_064_454),
  ("Nat.add", 259_113_366),
  ("Nat.add_comm", 453_346_760),
  ("Nat.decEq", 525_053_419),
  ("Nat.decLe", 1_060_359_340),
  ("Nat.sub_le_of_le_add", 2_324_843_242),
  ("Nat.shiftRight_succ", 395_364_332),
  ("Trans.mk", 209_760_732),
  ("Array.append_assoc", 11_077_462_383),
  ("Vector.append", 11_359_236_283),
  ("IxVMPrim.nat_add_lit", 251_857_899),
  ("IxVMPrim.nat_sub_lit", 251_891_464),
  ("IxVMPrim.nat_mul_lit", 224_240_532),
  ("IxVMPrim.nat_mul_big", 222_674_032),
  ("IxVMPrim.nat_div_lit", 229_620_342),
  ("IxVMPrim.nat_mod_lit", 229_833_783),
  ("IxVMPrim.nat_succ_lit", 220_856_399),
  ("IxVMPrim.nat_pred_lit", 224_033_901),
  ("IxVMPrim.nat_gcd_lit", 224_871_173),
  ("IxVMPrim.nat_land_lit", 221_924_397),
  ("IxVMPrim.nat_lor_lit", 223_538_860),
  ("IxVMPrim.nat_xor_lit", 225_001_036),
  ("IxVMPrim.nat_shl_lit", 224_945_294),
  ("IxVMPrim.nat_shr_lit", 225_097_541),
  ("IxVMPrim.nat_pow_big", 1_010_137_749),
  ("IxVMPrim.nat_beq_lit", 225_147_087),
  ("IxVMPrim.nat_ble_lit", 226_343_895),
  ("IxVMPrim.nat_cases_big", 248_775_471),
  ("IxVMPrim.nat_dec_le", 383_984_554),
  ("IxVMPrim.nat_dec_lt", 381_915_751),
  ("IxVMPrim.nat_dec_eq", 369_625_445),
  ("IxVMPrim.str_size_lit", 3_346_947_542),
  ("IxVMPrim.bv_to_nat_lit", 2_534_407_649),
  ("IxVMInd.Even", 245_471_628),
  ("IxVMInd.Odd", 245_478_133),
  ("IxVMInd.Even.rec", 269_911_826),
  ("IxVMInd.Odd.rec", 269_912_921),
  ("IxVMInd.IdxTeleN.rec", 244_800_454),
  ("IxVMInd.IdxTeleB.rec", 244_799_372),
  ("IxVMInd.SoloA.rec", 237_364_856),
  ("IxVMInd.SoloB.rec", 237_364_856),
  ("IxVMInd.UnsafeSquash", 202_293_852),
  ("IxVMInd.Tree", 201_750_744),
  ("IxVMInd.Tree.rec", 217_965_958),
  ("IxVMInd.DedupM", 206_472_487),
  ("IxVMInd.DedupM.rec", 227_791_638),
  ("IxVMInd.DepthM", 204_227_741),
  ("IxVMInd.DepthM.rec", 221_296_478),
  ("String.Internal.append", 2_978_395_243),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_307_758_126),
  ("Lean.Syntax.rec", 3_057_592_581),
  ("IxVMInd.AuxTie", 339_413_832),
  ("IxVMInd.AuxTie.rec", 398_609_181),
  ("IxVMInd.HiddenIdx", 200_772_345),
  ("IxVMInd.HiddenIdx.rec", 206_633_749),
  ("IxVMInd.thmMajorUse", 693_685_130),
  ("IxVMInd.partialKRec", 227_091_240),
  ("IxVMInd.deepRebase", 294_813_383),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_386_334_090),
  ("Lean.Widget.TaggedText.rec", 3_019_110_832),
  ("Lean.Doc.Part.rec", 3_078_284_104),
  ("Lean.Doc.Block.rec", 3_389_252_452),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 204_598_957),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 255_169_017),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 255_171_176),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 255_172_256),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 230_046_942),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 203_633_058),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 242_124_952),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 242_126_026),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 242_126_026),
  ("strOfListFoldSize", 3_354_870_552),
  ("strOfListFoldSizeAscii", 3_352_950_928),
  ("IxVMPrim.lazy_ble_offset", 258_241_364),
  ("IxVMPrim.lazy_unit_cast", 438_893_137),
  ("IxVMPrim.sizeof_unit", 242_750_186),
  ("IxVMPerf.let_continuations", 532_728_334),
  ("IxVMPerf.mul_row", 470_534_615),
  ("IxVMPerf.context_tower", 806_865_440),
  ("IxVMPerf.mul_wide", 325_561_507)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 228_283_124),
  ("IxVMPrim.nat_mul_lit", 336_334_817),
  ("IxVMPrim.nat_div_lit", 2_471_869_867),
  ("IxVMPrim.nat_land_lit", 8_610_943_204)]

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
             accept := true, expectedFftCost := some 133_760_220_096, witness := witness }

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
    return { c with expectedFftCost := some 445_575_720_489 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
