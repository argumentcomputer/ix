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
  ("HEq", 194_908_208),
  ("HEq.rec", 202_188_044),
  ("Eq.rec", 200_487_783),
  ("Nat", 194_638_166),
  ("Nat.add", 255_030_540),
  ("Nat.add_comm", 450_337_112),
  ("Nat.decEq", 526_881_449),
  ("Nat.decLe", 1_073_782_547),
  ("Nat.sub_le_of_le_add", 2_370_490_162),
  ("Nat.shiftRight_succ", 392_848_820),
  ("Trans.mk", 205_639_778),
  ("Array.append_assoc", 12_814_954_119),
  ("Vector.append", 13_096_750_286),
  ("IxVMPrim.nat_add_lit", 247_034_531),
  ("IxVMPrim.nat_sub_lit", 247_069_514),
  ("IxVMPrim.nat_mul_lit", 219_281_844),
  ("IxVMPrim.nat_mul_big", 217_738_311),
  ("IxVMPrim.nat_div_lit", 224_322_751),
  ("IxVMPrim.nat_mod_lit", 224_576_634),
  ("IxVMPrim.nat_succ_lit", 215_957_106),
  ("IxVMPrim.nat_pred_lit", 233_811_254),
  ("IxVMPrim.nat_gcd_lit", 219_876_897),
  ("IxVMPrim.nat_land_lit", 216_947_249),
  ("IxVMPrim.nat_lor_lit", 218_537_381),
  ("IxVMPrim.nat_xor_lit", 219_897_243),
  ("IxVMPrim.nat_shl_lit", 219_927_055),
  ("IxVMPrim.nat_shr_lit", 220_089_775),
  ("IxVMPrim.nat_pow_big", 1_004_744_896),
  ("IxVMPrim.nat_beq_lit", 220_089_617),
  ("IxVMPrim.nat_ble_lit", 221_252_490),
  ("IxVMPrim.nat_cases_big", 243_942_028),
  ("IxVMPrim.nat_dec_le", 292_759_596),
  ("IxVMPrim.nat_dec_lt", 304_608_921),
  ("IxVMPrim.nat_dec_eq", 263_700_062),
  ("IxVMPrim.str_size_lit", 3_690_762_925),
  ("IxVMPrim.bv_to_nat_lit", 2_557_030_409),
  ("IxVMInd.Even", 482_767_743),
  ("IxVMInd.Odd", 482_771_256),
  ("IxVMInd.Even.rec", 486_887_515),
  ("IxVMInd.Odd.rec", 486_885_173),
  ("IxVMInd.IdxTeleN.rec", 465_923_140),
  ("IxVMInd.IdxTeleB.rec", 465_919_638),
  ("IxVMInd.SoloA.rec", 376_627_846),
  ("IxVMInd.SoloB.rec", 376_622_125),
  ("IxVMInd.Tree", 663_634_646),
  ("IxVMInd.Tree.rec", 665_926_619),
  ("IxVMInd.DedupM", 837_878_998),
  ("IxVMInd.DedupM.rec", 841_527_461),
  ("IxVMInd.DepthM", 849_790_641),
  ("IxVMInd.DepthM.rec", 852_159_622),
  ("String.Internal.append", 3_004_927_826),
  ("Lean.Syntax.rec", 4_397_526_894),
  ("IxVMInd.AuxTie", 1_656_147_398),
  ("IxVMInd.AuxTie.rec", 1_666_992_588),
  ("IxVMInd.HiddenIdx", 196_343_807),
  ("IxVMInd.HiddenIdx.rec", 202_165_893),
  ("IxVMInd.thmMajorUse", 700_003_415),
  ("IxVMInd.partialKRec", 222_350_025),
  ("IxVMInd.deepRebase", 289_956_014),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_427_973_308),
  ("Lean.Widget.TaggedText.rec", 4_785_963_879),
  ("Lean.Doc.Part.rec", 25_944_022_872),
  ("Lean.Doc.Block.rec", 22_858_875_340),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_539_335_970),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_551_089_390),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_551_090_652),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_551_090_652),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 830_527_890),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_370_586_143),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_378_128_875),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_378_131_381),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_378_131_381),
  ("strOfListFoldSize", 3_823_601_435),
  ("strOfListFoldSizeAscii", 3_663_625_258),
  ("IxVMPrim.lazy_ble_offset", 253_078_144),
  ("IxVMPrim.lazy_unit_cast", 443_039_095),
  ("IxVMPrim.sizeof_unit", 237_362_451),
  ("IxVMPerf.let_continuations", 530_329_086),
  ("IxVMPerf.mul_row", 458_090_027),
  ("IxVMPerf.context_tower", 847_522_181),
  ("IxVMPerf.mul_wide", 320_930_522)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 223_441_124),
  ("IxVMPrim.nat_mul_lit", 333_347_037),
  ("IxVMPrim.nat_div_lit", 2_534_773_561),
  ("IxVMPrim.nat_land_lit", 9_109_375_133)]

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
             accept := true, expectedFftCost := some 135_503_363_422, witness := witness }

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
    return { c with expectedFftCost := some 442_983_622_963 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
