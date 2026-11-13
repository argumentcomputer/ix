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
  ("HEq", 184_199_238),
  ("HEq.rec", 191_378_172),
  ("Eq.rec", 189_672_214),
  ("Nat", 183_597_867),
  ("Nat.add", 243_700_582),
  ("Nat.add_comm", 430_443_102),
  ("Nat.decEq", 508_759_385),
  ("Nat.decLe", 1_039_556_119),
  ("Nat.sub_le_of_le_add", 2_265_921_414),
  ("Nat.shiftRight_succ", 370_864_069),
  ("Trans.mk", 195_118_770),
  ("Array.append_assoc", 12_373_584_715),
  ("Vector.append", 12_638_610_077),
  ("IxVMPrim.nat_add_lit", 234_097_807),
  ("IxVMPrim.nat_sub_lit", 234_146_785),
  ("IxVMPrim.nat_mul_lit", 207_105_395),
  ("IxVMPrim.nat_mul_big", 205_714_794),
  ("IxVMPrim.nat_div_lit", 211_043_433),
  ("IxVMPrim.nat_mod_lit", 211_347_056),
  ("IxVMPrim.nat_succ_lit", 204_302_229),
  ("IxVMPrim.nat_pred_lit", 222_239_906),
  ("IxVMPrim.nat_gcd_lit", 207_746_094),
  ("IxVMPrim.nat_land_lit", 205_155_570),
  ("IxVMPrim.nat_lor_lit", 206_312_930),
  ("IxVMPrim.nat_xor_lit", 207_493_329),
  ("IxVMPrim.nat_shl_lit", 207_727_873),
  ("IxVMPrim.nat_shr_lit", 207_973_866),
  ("IxVMPrim.nat_pow_big", 1_006_653_278),
  ("IxVMPrim.nat_beq_lit", 207_945_311),
  ("IxVMPrim.nat_ble_lit", 209_140_145),
  ("IxVMPrim.nat_cases_big", 233_012_803),
  ("IxVMPrim.nat_dec_le", 278_387_255),
  ("IxVMPrim.nat_dec_lt", 289_265_147),
  ("IxVMPrim.nat_dec_eq", 250_997_951),
  ("IxVMPrim.str_size_lit", 3_527_018_760),
  ("IxVMPrim.bv_to_nat_lit", 2_442_807_596),
  ("IxVMInd.Even", 415_689_410),
  ("IxVMInd.Odd", 415_687_177),
  ("IxVMInd.Even.rec", 417_394_800),
  ("IxVMInd.Odd.rec", 417_394_800),
  ("IxVMInd.IdxTeleN.rec", 408_380_991),
  ("IxVMInd.IdxTeleB.rec", 408_429_186),
  ("IxVMInd.SoloA.rec", 341_886_981),
  ("IxVMInd.SoloB.rec", 341_980_215),
  ("IxVMInd.Tree", 574_229_266),
  ("IxVMInd.Tree.rec", 575_276_882),
  ("IxVMInd.DedupM", 700_913_044),
  ("IxVMInd.DedupM.rec", 702_039_510),
  ("IxVMInd.DepthM", 753_768_043),
  ("IxVMInd.DepthM.rec", 754_765_513),
  ("String.Internal.append", 2_873_462_202),
  ("Lean.Syntax.rec", 4_020_058_877),
  ("IxVMInd.AuxTie", 1_423_641_629),
  ("IxVMInd.AuxTie.rec", 1_425_749_579),
  ("IxVMInd.HiddenIdx", 185_487_344),
  ("IxVMInd.HiddenIdx.rec", 191_350_993),
  ("IxVMInd.NestParIdx.rec", 943_638_156),
  ("IxVMInd.NestListIdx.rec", 866_624_146),
  ("IxVMInd.NestRefl.rec", 644_066_158),
  ("IxVMInd.NestReflOpt.rec", 542_286_205),
  ("IxVMInd.Phantom", 187_117_975),
  ("IxVMInd.thmMajorUse", 674_452_248),
  ("IxVMInd.partialKRec", 210_445_805),
  ("IxVMInd.deepRebase", 276_011_144),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_265_346_618),
  ("Lean.Widget.TaggedText.rec", 4_380_996_399),
  ("Lean.Doc.Part.rec", 21_497_887_356),
  ("Lean.Doc.Block.rec", 18_839_481_593),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_251_381_652),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_253_759_256),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_253_811_650),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_253_810_454),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 708_982_278),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_108_964_276),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_110_810_046),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_110_714_357),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_110_766_348),
  ("strOfListFoldSize", 3_659_461_899),
  ("strOfListFoldSizeAscii", 3_499_300_381),
  ("IxVMPrim.lazy_ble_offset", 239_491_735),
  ("IxVMPrim.lazy_unit_cast", 423_834_104),
  ("IxVMPrim.sizeof_unit", 224_977_410),
  ("IxVMPerf.let_continuations", 523_026_674),
  ("IxVMPerf.mul_row", 456_760_325),
  ("IxVMPerf.context_tower", 888_988_659),
  ("IxVMPerf.mul_wide", 310_463_863)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 211_951_630),
  ("IxVMPrim.nat_mul_lit", 320_169_072),
  ("IxVMPrim.nat_div_lit", 2_443_654_228),
  ("IxVMPrim.nat_land_lit", 8_847_581_591)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 599_935_815),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 605_176_361),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 912_339_490)]

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
             accept := true, expectedFftCost := some 129_199_456_530, witness := witness }

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
    return { c with expectedFftCost := some 428_487_738_390 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
