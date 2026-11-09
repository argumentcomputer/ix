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
  ("HEq", 226_915_813),
  ("HEq.rec", 234_577_852),
  ("Eq.rec", 232_902_436),
  ("Nat", 226_668_634),
  ("Nat.add", 290_806_895),
  ("Nat.add_comm", 498_985_687),
  ("Nat.decEq", 576_793_097),
  ("Nat.decLe", 1_176_666_271),
  ("Nat.sub_le_of_le_add", 2_573_190_124),
  ("Nat.shiftRight_succ", 440_114_062),
  ("Trans.mk", 237_830_068),
  ("Array.append_assoc", 18_445_568_368),
  ("Vector.append", 18_751_775_331),
  ("IxVMPrim.nat_add_lit", 283_661_837),
  ("IxVMPrim.nat_sub_lit", 283_695_294),
  ("IxVMPrim.nat_mul_lit", 254_240_743),
  ("IxVMPrim.nat_mul_big", 252_538_157),
  ("IxVMPrim.nat_div_lit", 260_298_812),
  ("IxVMPrim.nat_mod_lit", 260_512_256),
  ("IxVMPrim.nat_succ_lit", 250_441_360),
  ("IxVMPrim.nat_pred_lit", 254_094_411),
  ("IxVMPrim.nat_gcd_lit", 254_850_500),
  ("IxVMPrim.nat_land_lit", 251_721_279),
  ("IxVMPrim.nat_lor_lit", 253_472_447),
  ("IxVMPrim.nat_xor_lit", 255_153_657),
  ("IxVMPrim.nat_shl_lit", 254_933_340),
  ("IxVMPrim.nat_shr_lit", 255_074_505),
  ("IxVMPrim.nat_pow_big", 1_033_640_160),
  ("IxVMPrim.nat_beq_lit", 255_275_831),
  ("IxVMPrim.nat_ble_lit", 256_561_590),
  ("IxVMPrim.nat_cases_big", 280_426_488),
  ("IxVMPrim.nat_dec_le", 423_811_616),
  ("IxVMPrim.nat_dec_lt", 420_904_292),
  ("IxVMPrim.nat_dec_eq", 408_911_949),
  ("IxVMPrim.str_size_lit", 3_632_723_548),
  ("IxVMPrim.bv_to_nat_lit", 2_770_530_423),
  ("IxVMInd.Even", 276_906_587),
  ("IxVMInd.Odd", 276_913_092),
  ("IxVMInd.Even.rec", 303_018_728),
  ("IxVMInd.Odd.rec", 303_020_920),
  ("IxVMInd.IdxTeleN.rec", 275_840_078),
  ("IxVMInd.IdxTeleB.rec", 275_838_996),
  ("IxVMInd.SoloA.rec", 268_039_240),
  ("IxVMInd.SoloB.rec", 268_039_240),
  ("IxVMInd.UnsafeSquash", 230_270_294),
  ("IxVMInd.Tree", 229_589_149),
  ("IxVMInd.Tree.rec", 246_850_970),
  ("IxVMInd.DedupM", 234_837_691),
  ("IxVMInd.DedupM.rec", 257_428_008),
  ("IxVMInd.DepthM", 232_333_143),
  ("IxVMInd.DepthM.rec", 250_487_417),
  ("String.Internal.append", 3_241_748_142),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_593_777_628),
  ("Lean.Syntax.rec", 3_325_916_867),
  ("IxVMInd.AuxTie", 379_183_518),
  ("IxVMInd.AuxTie.rec", 441_527_888),
  ("IxVMInd.HiddenIdx", 228_548_600),
  ("IxVMInd.HiddenIdx.rec", 234_751_077),
  ("IxVMInd.thmMajorUse", 774_356_388),
  ("IxVMInd.partialKRec", 256_937_585),
  ("IxVMInd.deepRebase", 329_976_923),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_674_860_597),
  ("Lean.Widget.TaggedText.rec", 3_284_580_932),
  ("Lean.Doc.Part.rec", 3_347_074_514),
  ("Lean.Doc.Block.rec", 3_682_662_939),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 232_622_692),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 285_998_116),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 286_000_276),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 286_001_357),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 259_712_760),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 231_600_066),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 272_309_534),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 272_311_684),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 272_311_684),
  ("strOfListFoldSize", 3_641_418_044),
  ("strOfListFoldSizeAscii", 3_639_422_291),
  ("IxVMPrim.lazy_ble_offset", 291_052_521),
  ("IxVMPrim.lazy_unit_cast", 483_840_110),
  ("IxVMPrim.sizeof_unit", 274_287_227),
  ("IxVMPerf.let_continuations", 287_605_137),
  ("IxVMPerf.mul_row", 518_099_430),
  ("IxVMPerf.context_tower", 776_232_879),
  ("IxVMPerf.mul_wide", 358_794_501)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_285_503),
  ("IxVMPrim.nat_mul_lit", 370_714_346),
  ("IxVMPrim.nat_div_lit", 2_714_453_318),
  ("IxVMPrim.nat_land_lit", 10_100_282_022)]

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
             accept := true, expectedFftCost := some 195_479_228_707, witness := witness }

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
    return { c with expectedFftCost := some 1_068_163_271_641 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
