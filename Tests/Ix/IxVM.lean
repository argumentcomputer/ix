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
  ("HEq", 188_121_935),
  ("HEq.rec", 192_420_242),
  ("Eq.rec", 191_129_599),
  ("Nat", 188_026_063),
  ("Nat.add", 228_094_881),
  ("Nat.add_comm", 356_260_418),
  ("Nat.decEq", 407_516_062),
  ("Nat.decLe", 773_848_975),
  ("Nat.sub_le_of_le_add", 1_615_087_816),
  ("Nat.shiftRight_succ", 321_030_192),
  ("Trans.mk", 196_031_477),
  ("Array.append_assoc", 8_356_870_897),
  ("Vector.append", 8_534_402_063),
  ("IxVMPrim.nat_add_lit", 221_712_310),
  ("IxVMPrim.nat_sub_lit", 221_719_470),
  ("IxVMPrim.nat_mul_lit", 203_174_910),
  ("IxVMPrim.nat_mul_big", 202_216_677),
  ("IxVMPrim.nat_div_lit", 206_039_994),
  ("IxVMPrim.nat_mod_lit", 206_223_297),
  ("IxVMPrim.nat_succ_lit", 201_060_055),
  ("IxVMPrim.nat_pred_lit", 203_066_571),
  ("IxVMPrim.nat_gcd_lit", 203_445_170),
  ("IxVMPrim.nat_land_lit", 201_793_082),
  ("IxVMPrim.nat_lor_lit", 202_671_062),
  ("IxVMPrim.nat_xor_lit", 203_489_403),
  ("IxVMPrim.nat_shl_lit", 203_494_169),
  ("IxVMPrim.nat_shr_lit", 203_565_400),
  ("IxVMPrim.nat_pow_big", 256_086_238),
  ("IxVMPrim.nat_beq_lit", 203_587_222),
  ("IxVMPrim.nat_ble_lit", 204_373_485),
  ("IxVMPrim.nat_cases_big", 220_572_727),
  ("IxVMPrim.nat_dec_le", 256_338_867),
  ("IxVMPrim.nat_dec_lt", 263_820_801),
  ("IxVMPrim.nat_dec_eq", 235_581_565),
  ("IxVMPrim.str_size_lit", 2_004_791_175),
  ("IxVMPrim.bv_to_nat_lit", 1_710_067_402),
  ("IxVMInd.Even", 352_142_315),
  ("IxVMInd.Odd", 352_142_315),
  ("IxVMInd.Even.rec", 352_540_678),
  ("IxVMInd.Odd.rec", 352_540_678),
  ("IxVMInd.IdxTeleN.rec", 343_682_627),
  ("IxVMInd.IdxTeleB.rec", 343_682_627),
  ("IxVMInd.SoloA.rec", 298_809_940),
  ("IxVMInd.SoloB.rec", 298_809_940),
  ("IxVMInd.Tree", 434_942_964),
  ("IxVMInd.Tree.rec", 435_298_556),
  ("IxVMInd.DedupM", 519_145_459),
  ("IxVMInd.DedupM.rec", 519_517_738),
  ("IxVMInd.DepthM", 522_444_933),
  ("IxVMInd.DepthM.rec", 522_762_373),
  ("String.Internal.append", 2_015_660_200),
  ("Lean.Syntax.rec", 910_664_368),
  ("IxVMInd.AuxTie", 872_251_468),
  ("IxVMInd.AuxTie.rec", 872_905_321),
  ("IxVMInd.HiddenIdx", 189_082_175),
  ("IxVMInd.HiddenIdx.rec", 192_586_553),
  ("IxVMInd.NestParIdx.rec", 635_031_814),
  ("IxVMInd.NestListIdx.rec", 597_555_440),
  ("IxVMInd.NestRefl.rec", 475_624_501),
  ("IxVMInd.NestReflOpt.rec", 424_362_018),
  ("IxVMInd.thmMajorUse", 518_679_909),
  ("IxVMInd.partialKRec", 205_208_275),
  ("IxVMInd.deepRebase", 251_665_701),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 2_032_832_461),
  ("Lean.Widget.TaggedText.rec", 1_034_831_321),
  ("Lean.Doc.Part.rec", 9_585_545_818),
  ("Lean.Doc.Block.rec", 8_109_337_850),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 848_022_429),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 848_705_252),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 848_700_936),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 848_700_936),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 524_964_748),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 752_660_151),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 753_188_795),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 753_188_795),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 753_188_795),
  ("strOfListFoldSize", 213_025_462),
  ("strOfListFoldSizeAscii", 213_011_463),
  ("IxVMPrim.lazy_ble_offset", 225_712_274),
  ("IxVMPrim.lazy_unit_cast", 352_654_123),
  ("IxVMPrim.sizeof_unit", 215_297_956),
  ("IxVMPerf.let_continuations", 365_203_557),
  ("IxVMPerf.mul_row", 331_626_828),
  ("IxVMPerf.context_tower", 645_509_395),
  ("IxVMPerf.mul_wide", 248_513_816)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 207_019_418),
  ("IxVMPrim.nat_mul_lit", 277_642_349),
  ("IxVMPrim.nat_div_lit", 1_684_145_451),
  ("IxVMPrim.nat_land_lit", 5_094_966_182)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 454_977_719),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 455_768_299),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 637_417_124)]

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
             accept := true, expectedFftCost := some 84_321_983_556, witness := witness }

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
    return { c with expectedFftCost := some 274_706_794_397 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
