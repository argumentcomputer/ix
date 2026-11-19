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
  ("HEq", 194_180_033),
  ("HEq.rec", 200_499_166),
  ("Eq.rec", 197_785_394),
  ("Nat", 193_676_339),
  ("Nat.add", 251_671_727),
  ("Nat.add_comm", 439_755_091),
  ("Nat.decEq", 516_036_120),
  ("Nat.decLe", 1_048_998_616),
  ("Nat.sub_le_of_le_add", 2_279_804_282),
  ("Nat.shiftRight_succ", 380_215_372),
  ("Trans.mk", 204_481_828),
  ("Array.append_assoc", 12_431_190_185),
  ("Vector.append", 12_698_076_434),
  ("IxVMPrim.nat_add_lit", 243_844_272),
  ("IxVMPrim.nat_sub_lit", 243_892_695),
  ("IxVMPrim.nat_mul_lit", 215_941_839),
  ("IxVMPrim.nat_mul_big", 214_546_401),
  ("IxVMPrim.nat_div_lit", 219_862_472),
  ("IxVMPrim.nat_mod_lit", 220_167_851),
  ("IxVMPrim.nat_succ_lit", 212_813_619),
  ("IxVMPrim.nat_pred_lit", 230_641_079),
  ("IxVMPrim.nat_gcd_lit", 216_559_204),
  ("IxVMPrim.nat_land_lit", 213_990_258),
  ("IxVMPrim.nat_lor_lit", 215_149_866),
  ("IxVMPrim.nat_xor_lit", 216_332_451),
  ("IxVMPrim.nat_shl_lit", 216_538_353),
  ("IxVMPrim.nat_shr_lit", 216_780_186),
  ("IxVMPrim.nat_pow_big", 1_037_368_052),
  ("IxVMPrim.nat_beq_lit", 217_215_734),
  ("IxVMPrim.nat_ble_lit", 218_416_084),
  ("IxVMPrim.nat_cases_big", 240_616_312),
  ("IxVMPrim.nat_dec_le", 289_475_039),
  ("IxVMPrim.nat_dec_lt", 300_432_182),
  ("IxVMPrim.nat_dec_eq", 261_250_732),
  ("IxVMPrim.str_size_lit", 3_548_752_458),
  ("IxVMPrim.bv_to_nat_lit", 2_458_145_048),
  ("IxVMInd.Even", 427_729_400),
  ("IxVMInd.Odd", 427_727_167),
  ("IxVMInd.Even.rec", 428_452_330),
  ("IxVMInd.Odd.rec", 428_454_563),
  ("IxVMInd.IdxTeleN.rec", 417_804_763),
  ("IxVMInd.IdxTeleB.rec", 417_806_991),
  ("IxVMInd.SoloA.rec", 353_606_563),
  ("IxVMInd.SoloB.rec", 353_606_563),
  ("IxVMInd.Tree", 587_580_901),
  ("IxVMInd.Tree.rec", 588_229_060),
  ("IxVMInd.DedupM", 722_330_137),
  ("IxVMInd.DedupM.rec", 722_987_754),
  ("IxVMInd.DepthM", 768_467_028),
  ("IxVMInd.DepthM.rec", 769_073_797),
  ("String.Internal.append", 2_896_724_321),
  ("Lean.Syntax.rec", 4_068_670_484),
  ("IxVMInd.AuxTie", 1_468_700_407),
  ("IxVMInd.AuxTie.rec", 1_469_778_043),
  ("IxVMInd.HiddenIdx", 195_661_661),
  ("IxVMInd.HiddenIdx.rec", 200_758_565),
  ("IxVMInd.NestParIdx.rec", 952_343_188),
  ("IxVMInd.NestListIdx.rec", 876_827_630),
  ("IxVMInd.NestRefl.rec", 655_280_253),
  ("IxVMInd.NestReflOpt.rec", 556_576_232),
  ("IxVMInd.thmMajorUse", 682_861_357),
  ("IxVMInd.partialKRec", 219_025_959),
  ("IxVMInd.deepRebase", 285_393_703),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_287_096_814),
  ("Lean.Widget.TaggedText.rec", 4_410_313_541),
  ("Lean.Doc.Part.rec", 21_535_362_428),
  ("Lean.Doc.Block.rec", 18_860_429_666),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_271_836_844),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_272_884_859),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_272_886_054),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_272_883_663),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 727_196_503),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_126_691_326),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_127_481_638),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_127_482_823),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_127_485_193),
  ("strOfListFoldSize", 3_681_349_111),
  ("strOfListFoldSizeAscii", 3_521_081_719),
  ("IxVMPrim.lazy_ble_offset", 250_567_932),
  ("IxVMPrim.lazy_unit_cast", 433_774_541),
  ("IxVMPrim.sizeof_unit", 233_601_884),
  ("IxVMPerf.let_continuations", 531_086_369),
  ("IxVMPerf.mul_row", 462_726_026),
  ("IxVMPerf.context_tower", 897_279_696),
  ("IxVMPerf.mul_wide", 315_777_684)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 220_358_734),
  ("IxVMPrim.nat_mul_lit", 328_697_753),
  ("IxVMPrim.nat_div_lit", 2_458_925_320),
  ("IxVMPrim.nat_land_lit", 8_874_091_666)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 612_143_339),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 619_027_134),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 924_100_674)]

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
             accept := true, expectedFftCost := some 130_249_556_799, witness := witness }

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
    return { c with expectedFftCost := some 428_979_450_729 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return pinnedCheck fenv (nameOfString n) cost c
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
