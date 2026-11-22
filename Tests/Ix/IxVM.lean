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
  ("HEq", 150_483_265),
  ("HEq.rec", 154_308_603),
  ("Eq.rec", 153_146_737),
  ("Nat", 150_400_743),
  ("Nat.add", 186_329_284),
  ("Nat.add_comm", 301_473_741),
  ("Nat.decEq", 349_089_956),
  ("Nat.decLe", 679_157_953),
  ("Nat.sub_le_of_le_add", 1_439_571_457),
  ("Nat.shiftRight_succ", 268_997_144),
  ("Trans.mk", 157_582_026),
  ("Array.append_assoc", 7_595_019_646),
  ("Vector.append", 7_754_872_617),
  ("IxVMPrim.nat_add_lit", 180_502_809),
  ("IxVMPrim.nat_sub_lit", 180_509_731),
  ("IxVMPrim.nat_mul_lit", 163_881_396),
  ("IxVMPrim.nat_mul_big", 163_023_964),
  ("IxVMPrim.nat_div_lit", 166_420_442),
  ("IxVMPrim.nat_mod_lit", 166_580_264),
  ("IxVMPrim.nat_succ_lit", 162_001_731),
  ("IxVMPrim.nat_pred_lit", 163_778_065),
  ("IxVMPrim.nat_gcd_lit", 164_119_631),
  ("IxVMPrim.nat_land_lit", 162_648_337),
  ("IxVMPrim.nat_lor_lit", 163_434_759),
  ("IxVMPrim.nat_xor_lit", 164_161_453),
  ("IxVMPrim.nat_shl_lit", 164_161_161),
  ("IxVMPrim.nat_shr_lit", 164_223_719),
  ("IxVMPrim.nat_pow_big", 211_064_991),
  ("IxVMPrim.nat_beq_lit", 164_240_742),
  ("IxVMPrim.nat_ble_lit", 164_940_162),
  ("IxVMPrim.nat_cases_big", 179_426_638),
  ("IxVMPrim.nat_dec_le", 211_126_898),
  ("IxVMPrim.nat_dec_lt", 217_758_899),
  ("IxVMPrim.nat_dec_eq", 192_675_743),
  ("IxVMPrim.str_size_lit", 1_790_034_027),
  ("IxVMPrim.bv_to_nat_lit", 1_525_093_044),
  ("IxVMInd.Even", 296_705_822),
  ("IxVMInd.Odd", 296_705_822),
  ("IxVMInd.Even.rec", 297_065_554),
  ("IxVMInd.Odd.rec", 297_065_554),
  ("IxVMInd.IdxTeleN.rec", 289_337_923),
  ("IxVMInd.IdxTeleB.rec", 289_337_923),
  ("IxVMInd.SoloA.rec", 249_123_684),
  ("IxVMInd.SoloB.rec", 249_123_684),
  ("IxVMInd.Tree", 373_179_910),
  ("IxVMInd.Tree.rec", 373_502_221),
  ("IxVMInd.DedupM", 448_547_265),
  ("IxVMInd.DedupM.rec", 448_885_087),
  ("IxVMInd.DepthM", 454_933_681),
  ("IxVMInd.DepthM.rec", 455_221_529),
  ("String.Internal.append", 1_799_803_654),
  ("Lean.Syntax.rec", 802_368_039),
  ("IxVMInd.AuxTie", 767_255_386),
  ("IxVMInd.AuxTie.rec", 767_848_123),
  ("IxVMInd.HiddenIdx", 151_337_304),
  ("IxVMInd.HiddenIdx.rec", 154_449_796),
  ("IxVMInd.NestParIdx.rec", 560_688_558),
  ("IxVMInd.NestListIdx.rec", 524_611_722),
  ("IxVMInd.NestRefl.rec", 410_007_953),
  ("IxVMInd.NestReflOpt.rec", 362_848_431),
  ("IxVMInd.thmMajorUse", 448_933_297),
  ("IxVMInd.partialKRec", 165_735_899),
  ("IxVMInd.deepRebase", 207_258_764),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 1_815_114_584),
  ("Lean.Widget.TaggedText.rec", 923_225_477),
  ("Lean.Doc.Part.rec", 8_832_882_140),
  ("Lean.Doc.Block.rec", 7_464_582_010),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 748_323_313),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 748_942_991),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 748_939_175),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 748_939_175),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 454_065_032),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 661_325_855),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 661_805_572),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 661_805_572),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 661_805_572),
  ("strOfListFoldSize", 172_604_551),
  ("strOfListFoldSizeAscii", 172_592_681),
  ("IxVMPrim.lazy_ble_offset", 184_004_266),
  ("IxVMPrim.lazy_unit_cast", 297_725_715),
  ("IxVMPrim.sizeof_unit", 174_680_251),
  ("IxVMPerf.let_continuations", 323_273_014),
  ("IxVMPerf.mul_row", 278_717_189),
  ("IxVMPerf.context_tower", 576_428_448),
  ("IxVMPerf.mul_wide", 203_922_194)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 167_302_319),
  ("IxVMPrim.nat_mul_lit", 230_794_020),
  ("IxVMPrim.nat_div_lit", 1_507_059_564),
  ("IxVMPrim.nat_land_lit", 4_611_558_135)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 391_174_296),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 392_108_525),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 558_988_368)]

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
             accept := true, expectedFftCost := some 76_526_593_124, witness := witness }

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
    return { c with expectedFftCost := some 252_207_203_047 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
