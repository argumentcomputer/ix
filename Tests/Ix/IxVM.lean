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
  ("HEq", 150_482_676),
  ("HEq.rec", 154_306_489),
  ("Eq.rec", 153_145_788),
  ("Nat", 150_400_727),
  ("Nat.add", 186_339_900),
  ("Nat.add_comm", 301_261_693),
  ("Nat.decEq", 348_727_981),
  ("Nat.decLe", 678_341_976),
  ("Nat.sub_le_of_le_add", 1_437_638_204),
  ("Nat.shiftRight_succ", 268_792_340),
  ("Trans.mk", 157_575_431),
  ("Array.append_assoc", 7_613_984_428),
  ("Vector.append", 7_774_978_755),
  ("IxVMPrim.nat_add_lit", 180_509_706),
  ("IxVMPrim.nat_sub_lit", 180_516_629),
  ("IxVMPrim.nat_mul_lit", 163_881_524),
  ("IxVMPrim.nat_mul_big", 163_024_329),
  ("IxVMPrim.nat_div_lit", 166_420_569),
  ("IxVMPrim.nat_mod_lit", 166_580_391),
  ("IxVMPrim.nat_succ_lit", 162_002_201),
  ("IxVMPrim.nat_pred_lit", 163_778_514),
  ("IxVMPrim.nat_gcd_lit", 164_119_534),
  ("IxVMPrim.nat_land_lit", 162_648_495),
  ("IxVMPrim.nat_lor_lit", 163_434_946),
  ("IxVMPrim.nat_xor_lit", 164_161_640),
  ("IxVMPrim.nat_shl_lit", 164_159_909),
  ("IxVMPrim.nat_shr_lit", 164_223_210),
  ("IxVMPrim.nat_pow_big", 211_059_626),
  ("IxVMPrim.nat_beq_lit", 164_241_104),
  ("IxVMPrim.nat_ble_lit", 164_940_378),
  ("IxVMPrim.nat_cases_big", 179_409_173),
  ("IxVMPrim.nat_dec_le", 211_128_457),
  ("IxVMPrim.nat_dec_lt", 217_735_131),
  ("IxVMPrim.nat_dec_eq", 192_683_853),
  ("IxVMPrim.str_size_lit", 1_793_614_090),
  ("IxVMPrim.bv_to_nat_lit", 1_528_629_804),
  ("IxVMInd.Even", 296_730_544),
  ("IxVMInd.Odd", 296_730_544),
  ("IxVMInd.Even.rec", 297_090_113),
  ("IxVMInd.Odd.rec", 297_090_113),
  ("IxVMInd.IdxTeleN.rec", 289_346_650),
  ("IxVMInd.IdxTeleB.rec", 289_346_650),
  ("IxVMInd.SoloA.rec", 249_135_030),
  ("IxVMInd.SoloB.rec", 249_135_030),
  ("IxVMInd.Tree", 373_182_059),
  ("IxVMInd.Tree.rec", 373_504_219),
  ("IxVMInd.DedupM", 449_144_325),
  ("IxVMInd.DedupM.rec", 449_482_268),
  ("IxVMInd.DepthM", 456_565_316),
  ("IxVMInd.DepthM.rec", 456_853_526),
  ("String.Internal.append", 1_803_390_943),
  ("Lean.Syntax.rec", 802_186_318),
  ("IxVMInd.AuxTie", 766_683_289),
  ("IxVMInd.AuxTie.rec", 767_275_733),
  ("IxVMInd.HiddenIdx", 151_339_937),
  ("IxVMInd.HiddenIdx.rec", 154_453_075),
  ("IxVMInd.NestParIdx.rec", 560_540_419),
  ("IxVMInd.NestListIdx.rec", 524_512_521),
  ("IxVMInd.NestRefl.rec", 409_949_175),
  ("IxVMInd.NestReflOpt.rec", 362_859_197),
  ("IxVMInd.thmMajorUse", 448_719_106),
  ("IxVMInd.partialKRec", 165_730_569),
  ("IxVMInd.deepRebase", 207_247_314),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 1_818_708_519),
  ("Lean.Widget.TaggedText.rec", 922_858_436),
  ("Lean.Doc.Part.rec", 8_836_428_344),
  ("Lean.Doc.Block.rec", 7_464_973_380),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 748_547_165),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 749_162_984),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 749_162_984),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 749_162_984),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 454_153_229),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 661_524_616),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 662_000_556),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 662_000_556),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 662_000_556),
  ("strOfListFoldSize", 172_634_134),
  ("strOfListFoldSizeAscii", 172_622_264),
  ("IxVMPrim.lazy_ble_offset", 183_991_188),
  ("IxVMPrim.lazy_unit_cast", 297_765_968),
  ("IxVMPrim.sizeof_unit", 174_676_371),
  ("IxVMPerf.let_continuations", 323_272_984),
  ("IxVMPerf.mul_row", 278_440_896),
  ("IxVMPerf.context_tower", 576_428_052),
  ("IxVMPerf.mul_wide", 203_307_982)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 167_302_257),
  ("IxVMPrim.nat_mul_lit", 231_615_993),
  ("IxVMPrim.nat_div_lit", 1_518_669_418),
  ("IxVMPrim.nat_land_lit", 5_291_230_246)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 391_124_870),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 392_100_070),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 558_878_045)]

/-- Whether `name` is a recursor with two or more motives: a recursor of a mutual or nested
family, which the program refuses while `modeledRecursorsRefused`. -/
def isModeledRecursor (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match env.find? name with
  | some (.recInfo rv) => rv.numMotives > 1
  | _ => false

/-- A pinned check case as the program in force decides it: refused when it claims a recursor
of a mutual or nested family that the program refuses, else accepted at its FFT pin. -/
def pinnedCheck (env : Lean.Environment) (name : Lean.Name) (cost : Nat) (c : Case) : Case :=
  if modeledRecursorsRefused && isModeledRecursor env name then c.throughModeledRecursor
  else { c with expectedFftCost := some cost }

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
             accept := true, expectedFftCost := some 78_816_108_423, witness := witness }

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
    return pinnedCheck env (nameOfString n) cost c
  let validating := validatingCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase ixonEnv (nameOfString n) false u
    return pinnedCheck env (nameOfString n) cost c
  let binding : Builder := fun _ => do
    let ctx ← Ix.ClaimContext.ofEnv ixonEnv
    let c ← Case.ofClaim "binding claim for the default table" ixonEnv (.binding ctx.spec ctx.binding)
    return { c with expectedFftCost := some 256_895_015_030 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return pinnedCheck fenv (nameOfString n) cost c
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
