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
  ("HEq", 226_952_154),
  ("HEq.rec", 234_630_614),
  ("Eq.rec", 232_939_429),
  ("Nat", 226_701_502),
  ("Nat.add", 290_911_411),
  ("Nat.add_comm", 499_493_105),
  ("Nat.decEq", 577_196_305),
  ("Nat.decLe", 1_178_548_720),
  ("Nat.sub_le_of_le_add", 2_575_848_157),
  ("Nat.shiftRight_succ", 440_515_888),
  ("Trans.mk", 238_040_835),
  ("Array.append_assoc", 19_925_154_165),
  ("Vector.append", 20_234_647_110),
  ("IxVMPrim.nat_add_lit", 283_930_730),
  ("IxVMPrim.nat_sub_lit", 283_964_268),
  ("IxVMPrim.nat_mul_lit", 254_307_244),
  ("IxVMPrim.nat_mul_big", 252_604_366),
  ("IxVMPrim.nat_div_lit", 260_364_454),
  ("IxVMPrim.nat_mod_lit", 260_577_898),
  ("IxVMPrim.nat_succ_lit", 250_507_222),
  ("IxVMPrim.nat_pred_lit", 254_160_521),
  ("IxVMPrim.nat_gcd_lit", 254_916_206),
  ("IxVMPrim.nat_land_lit", 251_787_217),
  ("IxVMPrim.nat_lor_lit", 253_538_703),
  ("IxVMPrim.nat_xor_lit", 255_219_873),
  ("IxVMPrim.nat_shl_lit", 255_000_556),
  ("IxVMPrim.nat_shr_lit", 255_140_856),
  ("IxVMPrim.nat_pow_big", 1_034_187_711),
  ("IxVMPrim.nat_beq_lit", 255_379_919),
  ("IxVMPrim.nat_ble_lit", 256_666_089),
  ("IxVMPrim.nat_cases_big", 280_522_130),
  ("IxVMPrim.nat_dec_le", 424_421_771),
  ("IxVMPrim.nat_dec_lt", 421_520_432),
  ("IxVMPrim.nat_dec_eq", 409_256_929),
  ("IxVMPrim.str_size_lit", 3_638_837_199),
  ("IxVMPrim.bv_to_nat_lit", 2_774_326_786),
  ("IxVMInd.Even", 544_297_150),
  ("IxVMInd.Odd", 544_298_321),
  ("IxVMInd.Even.rec", 548_433_093),
  ("IxVMInd.Odd.rec", 548_434_264),
  ("IxVMInd.IdxTeleN.rec", 524_375_723),
  ("IxVMInd.IdxTeleB.rec", 524_378_058),
  ("IxVMInd.SoloA.rec", 427_671_129),
  ("IxVMInd.SoloB.rec", 427_671_129),
  ("IxVMInd.Tree", 690_420_572),
  ("IxVMInd.Tree.rec", 692_705_912),
  ("IxVMInd.DedupM", 867_241_603),
  ("IxVMInd.DedupM.rec", 870_861_632),
  ("IxVMInd.DepthM", 848_180_870),
  ("IxVMInd.DepthM.rec", 850_539_600),
  ("String.Internal.append", 3_247_707_940),
  ("Lean.Syntax.rec", 4_614_706_256),
  ("IxVMInd.AuxTie", 1_668_949_023),
  ("IxVMInd.AuxTie.rec", 1_679_685_450),
  ("IxVMInd.HiddenIdx", 228_591_194),
  ("IxVMInd.HiddenIdx.rec", 234_800_797),
  ("IxVMInd.thmMajorUse", 775_834_135),
  ("IxVMInd.partialKRec", 257_005_576),
  ("IxVMInd.deepRebase", 330_267_370),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_681_831_310),
  ("Lean.Widget.TaggedText.rec", 4_888_096_075),
  ("Lean.Doc.Part.rec", 24_173_306_975),
  ("Lean.Doc.Block.rec", 21_370_894_556),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_544_184_095),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_555_857_316),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_555_861_880),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_555_861_880),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 865_142_383),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_373_878_657),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_381_358_989),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_381_358_989),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_381_358_989),
  ("strOfListFoldSize", 3_647_514_304),
  ("strOfListFoldSizeAscii", 3_645_517_384),
  ("IxVMPrim.lazy_ble_offset", 291_368_580),
  ("IxVMPrim.lazy_unit_cast", 484_563_982),
  ("IxVMPrim.sizeof_unit", 274_459_039),
  ("IxVMPerf.let_continuations", 287_607_524),
  ("IxVMPerf.mul_row", 518_012_668),
  ("IxVMPerf.context_tower", 776_323_773),
  ("IxVMPerf.mul_wide", 358_503_712)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_461_554),
  ("IxVMPrim.nat_mul_lit", 371_132_368),
  ("IxVMPrim.nat_div_lit", 2_717_495_629),
  ("IxVMPrim.nat_land_lit", 10_106_934_171)]

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
             accept := true, expectedFftCost := some 197_243_710_308, witness := witness }

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
    return { c with expectedFftCost := some 1_070_105_352_792 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
