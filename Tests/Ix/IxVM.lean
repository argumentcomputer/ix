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
  ("HEq", 194_747_323),
  ("HEq.rec", 201_867_015),
  ("Eq.rec", 200_215_702),
  ("Nat", 194_513_440),
  ("Nat.add", 252_500_636),
  ("Nat.add_comm", 440_399_242),
  ("Nat.decEq", 511_392_324),
  ("Nat.decLe", 1_031_127_557),
  ("Nat.sub_le_of_le_add", 2_261_418_911),
  ("Nat.shiftRight_succ", 382_339_806),
  ("Trans.mk", 205_030_564),
  ("Array.append_assoc", 10_846_584_829),
  ("Vector.append", 11_120_171_013),
  ("IxVMPrim.nat_add_lit", 245_352_893),
  ("IxVMPrim.nat_sub_lit", 245_388_202),
  ("IxVMPrim.nat_mul_lit", 218_643_455),
  ("IxVMPrim.nat_mul_big", 217_106_189),
  ("IxVMPrim.nat_div_lit", 223_693_438),
  ("IxVMPrim.nat_mod_lit", 223_891_326),
  ("IxVMPrim.nat_succ_lit", 215_393_339),
  ("IxVMPrim.nat_pred_lit", 218_371_437),
  ("IxVMPrim.nat_gcd_lit", 219_275_240),
  ("IxVMPrim.nat_land_lit", 216_380_044),
  ("IxVMPrim.nat_lor_lit", 217_957_258),
  ("IxVMPrim.nat_xor_lit", 219_312_172),
  ("IxVMPrim.nat_shl_lit", 219_346_497),
  ("IxVMPrim.nat_shr_lit", 219_498_745),
  ("IxVMPrim.nat_pow_big", 1_002_361_160),
  ("IxVMPrim.nat_beq_lit", 219_428_750),
  ("IxVMPrim.nat_ble_lit", 220_586_497),
  ("IxVMPrim.nat_cases_big", 242_263_495),
  ("IxVMPrim.nat_dec_le", 372_777_101),
  ("IxVMPrim.nat_dec_lt", 370_942_485),
  ("IxVMPrim.nat_dec_eq", 358_969_255),
  ("IxVMPrim.str_size_lit", 3_247_580_216),
  ("IxVMPrim.bv_to_nat_lit", 2_463_012_769),
  ("IxVMInd.Even", 239_168_924),
  ("IxVMInd.Odd", 239_175_428),
  ("IxVMInd.Even.rec", 262_748_521),
  ("IxVMInd.Odd.rec", 262_749_617),
  ("IxVMInd.IdxTeleN.rec", 238_543_099),
  ("IxVMInd.IdxTeleB.rec", 238_542_017),
  ("IxVMInd.SoloA.rec", 231_337_814),
  ("IxVMInd.SoloB.rec", 231_337_814),
  ("IxVMInd.Tree", 197_086_923),
  ("IxVMInd.Tree.rec", 212_767_634),
  ("IxVMInd.DedupM", 201_620_154),
  ("IxVMInd.DedupM.rec", 222_298_460),
  ("IxVMInd.DepthM", 199_465_153),
  ("IxVMInd.DepthM.rec", 216_026_442),
  ("String.Internal.append", 2_892_376_097),
  ("Lean.Syntax.rec", 2_969_204_331),
  ("IxVMInd.AuxTie", 329_136_010),
  ("IxVMInd.AuxTie.rec", 386_722_289),
  ("IxVMInd.HiddenIdx", 196_166_466),
  ("IxVMInd.HiddenIdx.rec", 201_857_895),
  ("IxVMInd.thmMajorUse", 675_979_343),
  ("IxVMInd.partialKRec", 221_502_825),
  ("IxVMInd.deepRebase", 286_345_726),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_285_593_769),
  ("Lean.Widget.TaggedText.rec", 2_932_319_519),
  ("Lean.Doc.Part.rec", 2_990_006_924),
  ("Lean.Doc.Block.rec", 3_295_753_944),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 199_832_081),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 249_007_365),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 249_009_524),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 249_010_603),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 224_433_156),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 198_915_281),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 236_322_636),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 236_323_710),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 236_323_710),
  ("strOfListFoldSize", 3_255_230_404),
  ("strOfListFoldSizeAscii", 3_253_314_544),
  ("IxVMPrim.lazy_ble_offset", 251_246_772),
  ("IxVMPrim.lazy_unit_cast", 425_621_185),
  ("IxVMPrim.sizeof_unit", 236_310_590),
  ("IxVMPerf.let_continuations", 527_019_724),
  ("IxVMPerf.mul_row", 456_357_519),
  ("IxVMPerf.context_tower", 794_570_891),
  ("IxVMPerf.mul_wide", 318_934_577)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 222_609_256),
  ("IxVMPrim.nat_mul_lit", 327_964_685),
  ("IxVMPrim.nat_div_lit", 2_413_597_059),
  ("IxVMPrim.nat_land_lit", 8_444_381_196)]

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
             accept := true, expectedFftCost := some 130_863_396_907, witness := witness }

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
    return { c with expectedFftCost := some 438_943_198_383 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
