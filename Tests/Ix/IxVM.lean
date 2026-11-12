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
  ("HEq", 184_127_383),
  ("HEq.rec", 191_185_674),
  ("Eq.rec", 189_644_565),
  ("Nat", 183_410_703),
  ("Nat.add", 244_965_560),
  ("Nat.add_comm", 434_518_053),
  ("Nat.decEq", 514_279_182),
  ("Nat.decLe", 1_051_856_230),
  ("Nat.sub_le_of_le_add", 2_292_640_908),
  ("Nat.shiftRight_succ", 379_786_967),
  ("Trans.mk", 195_208_440),
  ("Array.append_assoc", 12_483_159_162),
  ("Vector.append", 12_749_950_778),
  ("IxVMPrim.nat_add_lit", 235_327_124),
  ("IxVMPrim.nat_sub_lit", 235_451_372),
  ("IxVMPrim.nat_mul_lit", 207_198_453),
  ("IxVMPrim.nat_mul_big", 205_845_365),
  ("IxVMPrim.nat_div_lit", 211_360_921),
  ("IxVMPrim.nat_mod_lit", 211_492_080),
  ("IxVMPrim.nat_succ_lit", 204_381_713),
  ("IxVMPrim.nat_pred_lit", 222_483_120),
  ("IxVMPrim.nat_gcd_lit", 207_963_149),
  ("IxVMPrim.nat_land_lit", 205_165_783),
  ("IxVMPrim.nat_lor_lit", 206_556_066),
  ("IxVMPrim.nat_xor_lit", 207_637_498),
  ("IxVMPrim.nat_shl_lit", 207_969_459),
  ("IxVMPrim.nat_shr_lit", 208_042_612),
  ("IxVMPrim.nat_pow_big", 991_461_179),
  ("IxVMPrim.nat_beq_lit", 208_160_363),
  ("IxVMPrim.nat_ble_lit", 209_253_869),
  ("IxVMPrim.nat_cases_big", 233_180_942),
  ("IxVMPrim.nat_dec_le", 281_294_744),
  ("IxVMPrim.nat_dec_lt", 292_323_156),
  ("IxVMPrim.nat_dec_eq", 252_686_983),
  ("IxVMPrim.str_size_lit", 3_575_984_847),
  ("IxVMPrim.bv_to_nat_lit", 2_476_695_473),
  ("IxVMInd.Even", 416_034_309),
  ("IxVMInd.Odd", 416_035_429),
  ("IxVMInd.Even.rec", 419_952_080),
  ("IxVMInd.Odd.rec", 420_000_388),
  ("IxVMInd.IdxTeleN.rec", 409_210_995),
  ("IxVMInd.IdxTeleB.rec", 409_215_457),
  ("IxVMInd.SoloA.rec", 341_387_558),
  ("IxVMInd.SoloB.rec", 341_387_558),
  ("IxVMInd.Tree", 570_526_516),
  ("IxVMInd.Tree.rec", 572_730_738),
  ("IxVMInd.DedupM", 697_780_631),
  ("IxVMInd.DedupM.rec", 701_262_535),
  ("IxVMInd.DepthM", 751_296_655),
  ("IxVMInd.DepthM.rec", 753_442_157),
  ("String.Internal.append", 2_915_107_449),
  ("Lean.Syntax.rec", 4_066_067_945),
  ("IxVMInd.AuxTie", 1_424_284_346),
  ("IxVMInd.AuxTie.rec", 1_435_145_114),
  ("IxVMInd.HiddenIdx", 185_557_184),
  ("IxVMInd.HiddenIdx.rec", 191_403_665),
  ("IxVMInd.NestParIdx.rec", 943_026_941),
  ("IxVMInd.NestListIdx.rec", 866_641_279),
  ("IxVMInd.NestRefl.rec", 643_574_977),
  ("IxVMInd.NestReflOpt.rec", 539_377_281),
  ("IxVMInd.Phantom", 186_845_084),
  ("IxVMInd.thmMajorUse", 681_243_817),
  ("IxVMInd.partialKRec", 210_478_167),
  ("IxVMInd.deepRebase", 279_133_960),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_313_136_107),
  ("Lean.Widget.TaggedText.rec", 4_418_746_762),
  ("Lean.Doc.Part.rec", 21_501_169_934),
  ("Lean.Doc.Block.rec", 18_912_284_778),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_252_602_437),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_264_231_406),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_264_230_207),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_264_229_008),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 709_985_925),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_105_821_665),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_113_347_409),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_113_346_223),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_113_443_011),
  ("strOfListFoldSize", 3_707_924_896),
  ("strOfListFoldSizeAscii", 3_548_546_691),
  ("IxVMPrim.lazy_ble_offset", 240_499_393),
  ("IxVMPrim.lazy_unit_cast", 428_415_045),
  ("IxVMPrim.sizeof_unit", 224_940_067),
  ("IxVMPerf.let_continuations", 518_262_200),
  ("IxVMPerf.mul_row", 419_819_267),
  ("IxVMPerf.context_tower", 879_732_335),
  ("IxVMPerf.mul_wide", 305_706_716)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 212_273_425),
  ("IxVMPrim.nat_mul_lit", 321_627_726),
  ("IxVMPrim.nat_div_lit", 2_465_975_900),
  ("IxVMPrim.nat_land_lit", 8_892_208_142)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 599_353_160),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 605_939_194),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 912_494_325)]

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
             accept := true, expectedFftCost := some 129_734_748_126, witness := witness }

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
    return { c with expectedFftCost := some 428_654_424_172 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
