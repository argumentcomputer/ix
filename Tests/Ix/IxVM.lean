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
  ("HEq", 197_874_028),
  ("HEq.rec", 204_816_218),
  ("Eq.rec", 203_184_708),
  ("Nat", 197_667_263),
  ("Nat.add", 255_662_717),
  ("Nat.add_comm", 443_685_534),
  ("Nat.decEq", 512_487_376),
  ("Nat.decLe", 1_028_790_377),
  ("Nat.sub_le_of_le_add", 2_250_474_640),
  ("Nat.shiftRight_succ", 386_014_514),
  ("Trans.mk", 208_116_383),
  ("Array.append_assoc", 11_946_182_128),
  ("Vector.append", 12_213_610_212),
  ("IxVMPrim.nat_add_lit", 248_390_168),
  ("IxVMPrim.nat_sub_lit", 248_425_520),
  ("IxVMPrim.nat_mul_lit", 221_714_717),
  ("IxVMPrim.nat_mul_big", 220_237_005),
  ("IxVMPrim.nat_div_lit", 226_772_839),
  ("IxVMPrim.nat_mod_lit", 226_970_704),
  ("IxVMPrim.nat_succ_lit", 218_523_763),
  ("IxVMPrim.nat_pred_lit", 221_493_848),
  ("IxVMPrim.nat_gcd_lit", 222_357_318),
  ("IxVMPrim.nat_land_lit", 219_505_806),
  ("IxVMPrim.nat_lor_lit", 221_028_408),
  ("IxVMPrim.nat_xor_lit", 222_387_554),
  ("IxVMPrim.nat_shl_lit", 222_432_258),
  ("IxVMPrim.nat_shr_lit", 222_581_664),
  ("IxVMPrim.nat_pow_big", 1_005_638_483),
  ("IxVMPrim.nat_beq_lit", 222_599_300),
  ("IxVMPrim.nat_ble_lit", 223_699_699),
  ("IxVMPrim.nat_cases_big", 245_453_911),
  ("IxVMPrim.nat_dec_le", 375_487_164),
  ("IxVMPrim.nat_dec_lt", 373_798_161),
  ("IxVMPrim.nat_dec_eq", 361_511_291),
  ("IxVMPrim.str_size_lit", 2_846_048_789),
  ("IxVMPrim.bv_to_nat_lit", 2_431_045_890),
  ("IxVMInd.Even", 475_406_681),
  ("IxVMInd.Odd", 475_409_023),
  ("IxVMInd.Even.rec", 479_527_292),
  ("IxVMInd.Odd.rec", 479_524_951),
  ("IxVMInd.IdxTeleN.rec", 459_422_700),
  ("IxVMInd.IdxTeleB.rec", 459_425_034),
  ("IxVMInd.SoloA.rec", 372_818_811),
  ("IxVMInd.SoloB.rec", 372_818_811),
  ("IxVMInd.Tree", 628_582_304),
  ("IxVMInd.Tree.rec", 630_902_991),
  ("IxVMInd.DedupM", 793_134_106),
  ("IxVMInd.DedupM.rec", 796_748_626),
  ("IxVMInd.DepthM", 789_110_439),
  ("IxVMInd.DepthM.rec", 791_469_929),
  ("String.Internal.append", 2_858_040_235),
  ("Lean.Syntax.rec", 4_142_964_062),
  ("IxVMInd.AuxTie", 1_530_526_676),
  ("IxVMInd.AuxTie.rec", 1_541_300_177),
  ("IxVMInd.HiddenIdx", 199_325_793),
  ("IxVMInd.HiddenIdx.rec", 204_881_195),
  ("IxVMInd.thmMajorUse", 673_929_201),
  ("IxVMInd.partialKRec", 224_623_110),
  ("IxVMInd.deepRebase", 289_463_486),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 2_884_700_985),
  ("Lean.Widget.TaggedText.rec", 4_407_199_367),
  ("Lean.Doc.Part.rec", 21_034_889_833),
  ("Lean.Doc.Block.rec", 18_368_301_089),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_401_691_026),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_413_391_252),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_413_392_512),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_413_393_773),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 784_254_836),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_246_196_352),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_253_710_469),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_253_710_469),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_253_710_469),
  ("strOfListFoldSize", 3_221_754_389),
  ("strOfListFoldSizeAscii", 3_219_751_728),
  ("IxVMPrim.lazy_ble_offset", 254_445_497),
  ("IxVMPrim.lazy_unit_cast", 427_841_766),
  ("IxVMPrim.sizeof_unit", 239_619_523),
  ("IxVMPerf.let_continuations", 530_205_704),
  ("IxVMPerf.mul_row", 456_230_494),
  ("IxVMPerf.context_tower", 797_748_940),
  ("IxVMPerf.mul_wide", 321_434_871)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 226_071_807),
  ("IxVMPrim.nat_mul_lit", 330_711_530),
  ("IxVMPrim.nat_div_lit", 2_378_291_419),
  ("IxVMPrim.nat_land_lit", 7_781_547_324)]

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
             accept := true, expectedFftCost := some 127_337_293_756, witness := witness }

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
    return { c with expectedFftCost := some 430_646_397_746 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
