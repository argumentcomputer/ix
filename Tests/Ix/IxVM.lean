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
  ("HEq", 226_947_308),
  ("HEq.rec", 234_627_300),
  ("Eq.rec", 232_937_936),
  ("Nat", 226_695_096),
  ("Nat.add", 290_907_435),
  ("Nat.add_comm", 499_478_730),
  ("Nat.decEq", 577_179_759),
  ("Nat.decLe", 1_178_491_531),
  ("Nat.sub_le_of_le_add", 2_575_772_467),
  ("Nat.shiftRight_succ", 440_505_589),
  ("Trans.mk", 238_035_933),
  ("Array.append_assoc", 19_924_530_639),
  ("Vector.append", 20_234_014_638),
  ("IxVMPrim.nat_add_lit", 283_921_212),
  ("IxVMPrim.nat_sub_lit", 283_954_750),
  ("IxVMPrim.nat_mul_lit", 254_303_522),
  ("IxVMPrim.nat_mul_big", 252_600_644),
  ("IxVMPrim.nat_div_lit", 260_360_732),
  ("IxVMPrim.nat_mod_lit", 260_574_176),
  ("IxVMPrim.nat_succ_lit", 250_503_500),
  ("IxVMPrim.nat_pred_lit", 254_156_799),
  ("IxVMPrim.nat_gcd_lit", 254_912_484),
  ("IxVMPrim.nat_land_lit", 251_783_495),
  ("IxVMPrim.nat_lor_lit", 253_534_981),
  ("IxVMPrim.nat_xor_lit", 255_216_151),
  ("IxVMPrim.nat_shl_lit", 254_996_834),
  ("IxVMPrim.nat_shr_lit", 255_137_134),
  ("IxVMPrim.nat_pow_big", 1_034_171_132),
  ("IxVMPrim.nat_beq_lit", 255_370_138),
  ("IxVMPrim.nat_ble_lit", 256_656_307),
  ("IxVMPrim.nat_cases_big", 280_517_893),
  ("IxVMPrim.nat_dec_le", 424_396_718),
  ("IxVMPrim.nat_dec_lt", 421_495_302),
  ("IxVMPrim.nat_dec_eq", 409_240_556),
  ("IxVMPrim.str_size_lit", 3_638_695_182),
  ("IxVMPrim.bv_to_nat_lit", 2_774_231_661),
  ("IxVMInd.Even", 544_235_167),
  ("IxVMInd.Odd", 544_236_338),
  ("IxVMInd.Even.rec", 548_368_054),
  ("IxVMInd.Odd.rec", 548_369_225),
  ("IxVMInd.IdxTeleN.rec", 524_314_029),
  ("IxVMInd.IdxTeleB.rec", 524_316_364),
  ("IxVMInd.SoloA.rec", 427_619_525),
  ("IxVMInd.SoloB.rec", 427_619_525),
  ("IxVMInd.UnsafeSquash", 230_329_064),
  ("IxVMInd.Tree", 690_125_243),
  ("IxVMInd.Tree.rec", 692_396_107),
  ("IxVMInd.DedupM", 866_915_107),
  ("IxVMInd.DedupM.rec", 870_524_367),
  ("IxVMInd.DepthM", 847_869_280),
  ("IxVMInd.DepthM.rec", 850_227_759),
  ("String.Internal.append", 3_247_563_687),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_600_384_950),
  ("Lean.Syntax.rec", 4_614_221_662),
  ("IxVMInd.AuxTie", 1_668_515_085),
  ("IxVMInd.AuxTie.rec", 1_679_234_842),
  ("IxVMInd.HiddenIdx", 228_586_292),
  ("IxVMInd.HiddenIdx.rec", 234_797_425),
  ("IxVMInd.thmMajorUse", 775_791_782),
  ("IxVMInd.partialKRec", 257_001_791),
  ("IxVMInd.deepRebase", 330_257_572),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_681_677_937),
  ("Lean.Widget.TaggedText.rec", 4_887_701_113),
  ("Lean.Doc.Part.rec", 24_172_377_111),
  ("Lean.Doc.Block.rec", 21_370_098_849),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_543_832_939),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_555_491_971),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_555_495_274),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_555_496_535),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 864_805_858),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_373_539_305),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_381_009_156),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_381_009_156),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_381_009_156),
  ("strOfListFoldSize", 3_647_372_287),
  ("strOfListFoldSizeAscii", 3_645_375_367),
  ("IxVMPrim.lazy_ble_offset", 291_351_729),
  ("IxVMPrim.lazy_unit_cast", 484_535_464),
  ("IxVMPrim.sizeof_unit", 274_452_191),
  ("IxVMPerf.let_continuations", 287_606_264),
  ("IxVMPerf.mul_row", 518_007_890),
  ("IxVMPerf.context_tower", 776_319_469),
  ("IxVMPerf.mul_wide", 358_499_989)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_448_575),
  ("IxVMPrim.nat_mul_lit", 371_110_568),
  ("IxVMPrim.nat_div_lit", 2_717_398_161),
  ("IxVMPrim.nat_land_lit", 10_106_771_914)]

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
             accept := true, expectedFftCost := some 197_240_866_989, witness := witness }

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
    return { c with expectedFftCost := some 1_070_103_042_293 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
