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
  ("HEq", 194_876_169),
  ("HEq.rec", 202_160_573),
  ("Eq.rec", 200_468_800),
  ("Nat", 194_607_729),
  ("Nat.add", 255_080_390),
  ("Nat.add_comm", 450_386_629),
  ("Nat.decEq", 527_131_185),
  ("Nat.decLe", 1_073_655_789),
  ("Nat.sub_le_of_le_add", 2_357_744_165),
  ("Nat.shiftRight_succ", 389_629_455),
  ("Trans.mk", 205_479_761),
  ("Array.append_assoc", 11_348_788_809),
  ("Vector.append", 11_632_887_544),
  ("IxVMPrim.nat_add_lit", 246_846_088),
  ("IxVMPrim.nat_sub_lit", 246_881_596),
  ("IxVMPrim.nat_mul_lit", 219_245_255),
  ("IxVMPrim.nat_mul_big", 217_697_843),
  ("IxVMPrim.nat_div_lit", 224_299_077),
  ("IxVMPrim.nat_mod_lit", 224_552_960),
  ("IxVMPrim.nat_succ_lit", 215_915_066),
  ("IxVMPrim.nat_pred_lit", 218_953_646),
  ("IxVMPrim.nat_gcd_lit", 219_871_247),
  ("IxVMPrim.nat_land_lit", 216_913_221),
  ("IxVMPrim.nat_lor_lit", 218_500_009),
  ("IxVMPrim.nat_xor_lit", 219_859_192),
  ("IxVMPrim.nat_shl_lit", 219_954_520),
  ("IxVMPrim.nat_shr_lit", 220_107_951),
  ("IxVMPrim.nat_pow_big", 1_005_342_435),
  ("IxVMPrim.nat_beq_lit", 220_014_957),
  ("IxVMPrim.nat_ble_lit", 221_182_333),
  ("IxVMPrim.nat_cases_big", 243_897_389),
  ("IxVMPrim.nat_dec_le", 380_516_502),
  ("IxVMPrim.nat_dec_lt", 378_705_061),
  ("IxVMPrim.nat_dec_eq", 366_414_795),
  ("IxVMPrim.str_size_lit", 3_388_516_264),
  ("IxVMPrim.bv_to_nat_lit", 2_572_299_399),
  ("IxVMInd.Even", 240_441_584),
  ("IxVMInd.Odd", 240_448_088),
  ("IxVMInd.Even.rec", 264_713_246),
  ("IxVMInd.Odd.rec", 264_712_151),
  ("IxVMInd.IdxTeleN.rec", 239_643_397),
  ("IxVMInd.IdxTeleB.rec", 239_643_397),
  ("IxVMInd.SoloA.rec", 232_161_555),
  ("IxVMInd.SoloB.rec", 232_162_634),
  ("IxVMInd.UnsafeSquash", 197_730_221),
  ("IxVMInd.Tree", 197_219_234),
  ("IxVMInd.Tree.rec", 213_451_837),
  ("IxVMInd.DedupM", 201_760_268),
  ("IxVMInd.DedupM.rec", 223_341_604),
  ("IxVMInd.DepthM", 199_604_662),
  ("IxVMInd.DepthM.rec", 216_670_281),
  ("String.Internal.append", 3_018_980_708),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_350_289_087),
  ("Lean.Syntax.rec", 3_099_500_937),
  ("IxVMInd.AuxTie", 332_149_845),
  ("IxVMInd.AuxTie.rec", 393_367_353),
  ("IxVMInd.HiddenIdx", 196_305_709),
  ("IxVMInd.HiddenIdx.rec", 202_139_245),
  ("IxVMInd.thmMajorUse", 699_277_280),
  ("IxVMInd.partialKRec", 222_335_657),
  ("IxVMInd.deepRebase", 289_771_727),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_427_761_686),
  ("Lean.Widget.TaggedText.rec", 3_061_595_479),
  ("Lean.Doc.Part.rec", 3_120_122_057),
  ("Lean.Doc.Block.rec", 3_452_947_234),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 199_979_846),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 252_306_688),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 252_309_926),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 252_311_006),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 225_626_714),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 199_058_633),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 238_671_549),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 238_674_772),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 238_674_772),
  ("strOfListFoldSize", 3_396_186_249),
  ("strOfListFoldSizeAscii", 3_394_278_598),
  ("IxVMPrim.lazy_ble_offset", 252_838_852),
  ("IxVMPrim.lazy_unit_cast", 435_035_450),
  ("IxVMPrim.sizeof_unit", 237_248_001),
  ("IxVMPerf.let_continuations", 530_323_444),
  ("IxVMPerf.mul_row", 458_105_551),
  ("IxVMPerf.context_tower", 847_444_302),
  ("IxVMPerf.mul_wide", 320_021_526)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 223_334_293),
  ("IxVMPrim.nat_mul_lit", 333_470_799),
  ("IxVMPrim.nat_div_lit", 2_550_980_204),
  ("IxVMPrim.nat_land_lit", 9_452_599_424)]

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
             accept := true, expectedFftCost := some 135_920_477_377, witness := witness }

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
    return { c with expectedFftCost := some 450_977_286_249 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
