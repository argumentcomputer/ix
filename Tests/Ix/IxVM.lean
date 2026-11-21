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
  ("HEq", 154_063_038),
  ("HEq.rec", 158_121_734),
  ("Eq.rec", 156_936_262),
  ("Nat", 153_992_915),
  ("Nat.add", 192_427_374),
  ("Nat.add_comm", 314_574_557),
  ("Nat.decEq", 363_705_662),
  ("Nat.decLe", 710_402_488),
  ("Nat.sub_le_of_le_add", 1_507_134_973),
  ("Nat.shiftRight_succ", 280_994_082),
  ("Trans.mk", 161_415_970),
  ("Array.append_assoc", 7_949_965_596),
  ("Vector.append", 8_119_504_384),
  ("IxVMPrim.nat_add_lit", 186_375_150),
  ("IxVMPrim.nat_sub_lit", 186_380_464),
  ("IxVMPrim.nat_mul_lit", 168_698_028),
  ("IxVMPrim.nat_mul_big", 167_769_832),
  ("IxVMPrim.nat_div_lit", 171_514_800),
  ("IxVMPrim.nat_mod_lit", 171_680_726),
  ("IxVMPrim.nat_succ_lit", 166_649_083),
  ("IxVMPrim.nat_pred_lit", 168_625_011),
  ("IxVMPrim.nat_gcd_lit", 168_935_746),
  ("IxVMPrim.nat_land_lit", 167_383_234),
  ("IxVMPrim.nat_lor_lit", 168_237_079),
  ("IxVMPrim.nat_xor_lit", 169_036_756),
  ("IxVMPrim.nat_shl_lit", 168_981_078),
  ("IxVMPrim.nat_shr_lit", 169_049_079),
  ("IxVMPrim.nat_pow_big", 218_608_555),
  ("IxVMPrim.nat_beq_lit", 169_135_052),
  ("IxVMPrim.nat_ble_lit", 169_914_982),
  ("IxVMPrim.nat_cases_big", 185_355_950),
  ("IxVMPrim.nat_dec_le", 219_907_905),
  ("IxVMPrim.nat_dec_lt", 226_944_135),
  ("IxVMPrim.nat_dec_eq", 199_925_010),
  ("IxVMPrim.str_size_lit", 1_883_989_619),
  ("IxVMPrim.bv_to_nat_lit", 1_604_161_641),
  ("IxVMInd.Even", 311_803_192),
  ("IxVMInd.Odd", 311_800_958),
  ("IxVMInd.Even.rec", 312_163_636),
  ("IxVMInd.Odd.rec", 312_165_869),
  ("IxVMInd.IdxTeleN.rec", 303_935_510),
  ("IxVMInd.IdxTeleB.rec", 303_937_737),
  ("IxVMInd.SoloA.rec", 260_708_387),
  ("IxVMInd.SoloB.rec", 260_708_387),
  ("IxVMInd.Tree", 399_977_800),
  ("IxVMInd.Tree.rec", 400_302_927),
  ("IxVMInd.DedupM", 485_899_322),
  ("IxVMInd.DedupM.rec", 486_238_113),
  ("IxVMInd.DepthM", 514_798_330),
  ("IxVMInd.DepthM.rec", 515_093_318),
  ("String.Internal.append", 1_894_102_095),
  ("Lean.Syntax.rec", 875_291_166),
  ("IxVMInd.AuxTie", 848_621_650),
  ("IxVMInd.AuxTie.rec", 849_222_659),
  ("IxVMInd.HiddenIdx", 154_991_761),
  ("IxVMInd.HiddenIdx.rec", 158_314_836),
  ("IxVMInd.NestParIdx.rec", 618_436_977),
  ("IxVMInd.NestListIdx.rec", 576_567_125),
  ("IxVMInd.NestRefl.rec", 440_048_001),
  ("IxVMInd.NestReflOpt.rec", 387_161_551),
  ("IxVMInd.thmMajorUse", 467_791_498),
  ("IxVMInd.partialKRec", 170_578_190),
  ("IxVMInd.deepRebase", 214_990_743),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 1_910_513_362),
  ("Lean.Widget.TaggedText.rec", 1_026_981_733),
  ("Lean.Doc.Part.rec", 9_832_781_554),
  ("Lean.Doc.Block.rec", 8_225_479_273),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 808_290_328),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 808_911_711),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 808_912_902),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 808_910_520),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 487_946_008),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 716_385_344),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 716_861_881),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 716_863_061),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 716_865_421),
  ("strOfListFoldSize", 178_546_484),
  ("strOfListFoldSizeAscii", 178_531_611),
  ("IxVMPrim.lazy_ble_offset", 190_268_961),
  ("IxVMPrim.lazy_unit_cast", 311_616_129),
  ("IxVMPrim.sizeof_unit", 180_393_489),
  ("IxVMPerf.let_continuations", 349_978_988),
  ("IxVMPerf.mul_row", 289_228_893),
  ("IxVMPerf.context_tower", 613_752_276),
  ("IxVMPerf.mul_wide", 210_511_318)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 172_268_026),
  ("IxVMPrim.nat_mul_lit", 240_138_370),
  ("IxVMPrim.nat_div_lit", 1_587_931_719),
  ("IxVMPrim.nat_land_lit", 5_519_097_865)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 419_380_245),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 420_269_073),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 605_809_947)]

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
             accept := true, expectedFftCost := some 82_577_053_162, witness := witness }

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
    return { c with expectedFftCost := some 267_975_564_420 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return pinnedCheck fenv (nameOfString n) cost c
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
