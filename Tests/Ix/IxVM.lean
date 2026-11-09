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
  ("HEq", 226_719_113),
  ("HEq.rec", 234_511_113),
  ("Eq.rec", 232_614_085),
  ("Nat", 226_635_525),
  ("Nat.add", 290_150_865),
  ("Nat.add_comm", 495_286_140),
  ("Nat.decEq", 566_398_941),
  ("Nat.decLe", 1_151_157_089),
  ("Nat.sub_le_of_le_add", 2_479_302_498),
  ("Nat.shiftRight_succ", 437_249_122),
  ("Trans.mk", 237_762_053),
  ("Array.append_assoc", 11_813_195_218),
  ("Vector.append", 12_106_144_006),
  ("IxVMPrim.nat_add_lit", 283_463_426),
  ("IxVMPrim.nat_sub_lit", 283_496_884),
  ("IxVMPrim.nat_mul_lit", 254_138_988),
  ("IxVMPrim.nat_mul_big", 252_441_739),
  ("IxVMPrim.nat_div_lit", 260_159_718),
  ("IxVMPrim.nat_mod_lit", 260_411_151),
  ("IxVMPrim.nat_succ_lit", 250_364_986),
  ("IxVMPrim.nat_pred_lit", 254_014_266),
  ("IxVMPrim.nat_gcd_lit", 254_756_817),
  ("IxVMPrim.nat_land_lit", 251_626_687),
  ("IxVMPrim.nat_lor_lit", 253_382_866),
  ("IxVMPrim.nat_xor_lit", 255_062_676),
  ("IxVMPrim.nat_shl_lit", 254_831_717),
  ("IxVMPrim.nat_shr_lit", 254_974_973),
  ("IxVMPrim.nat_pow_big", 1_038_586_752),
  ("IxVMPrim.nat_beq_lit", 255_204_636),
  ("IxVMPrim.nat_ble_lit", 256_493_877),
  ("IxVMPrim.nat_cases_big", 280_088_246),
  ("IxVMPrim.nat_dec_le", 420_929_185),
  ("IxVMPrim.nat_dec_lt", 418_293_643),
  ("IxVMPrim.nat_dec_eq", 406_680_503),
  ("IxVMPrim.str_size_lit", 3_539_828_341),
  ("IxVMPrim.bv_to_nat_lit", 2_695_509_141),
  ("IxVMInd.Even", 274_687_930),
  ("IxVMInd.Odd", 274_693_349),
  ("IxVMInd.Even.rec", 302_227_300),
  ("IxVMInd.Odd.rec", 302_228_396),
  ("IxVMInd.IdxTeleN.rec", 275_440_602),
  ("IxVMInd.IdxTeleB.rec", 275_439_520),
  ("IxVMInd.SoloA.rec", 267_689_374),
  ("IxVMInd.SoloB.rec", 267_689_374),
  ("IxVMInd.UnsafeSquash", 230_188_939),
  ("IxVMInd.Tree", 229_338_239),
  ("IxVMInd.Tree.rec", 246_584_795),
  ("IxVMInd.DedupM", 234_517_184),
  ("IxVMInd.DedupM.rec", 256_985_268),
  ("IxVMInd.DepthM", 231_981_458),
  ("IxVMInd.DepthM.rec", 250_080_315),
  ("String.Internal.append", 3_156_412_781),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_502_693_213),
  ("Lean.Syntax.rec", 3_238_529_154),
  ("IxVMInd.AuxTie", 376_162_982),
  ("IxVMInd.AuxTie.rec", 437_921_385),
  ("IxVMInd.HiddenIdx", 228_348_738),
  ("IxVMInd.HiddenIdx.rec", 234_699_535),
  ("IxVMInd.thmMajorUse", 757_003_109),
  ("IxVMInd.partialKRec", 256_630_564),
  ("IxVMInd.deepRebase", 329_162_298),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_581_081_749),
  ("Lean.Widget.TaggedText.rec", 3_197_689_748),
  ("Lean.Doc.Part.rec", 3_254_972_523),
  ("Lean.Doc.Block.rec", 3_574_827_491),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 232_295_579),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 284_922_952),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 284_925_112),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 284_926_191),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 259_302_651),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 231_294_017),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 271_447_879),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 271_448_953),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 271_448_953),
  ("strOfListFoldSize", 3_548_515_807),
  ("strOfListFoldSizeAscii", 3_546_528_217),
  ("IxVMPrim.lazy_ble_offset", 290_805_825),
  ("IxVMPrim.lazy_unit_cast", 480_854_659),
  ("IxVMPrim.sizeof_unit", 274_162_004),
  ("IxVMPerf.let_continuations", 287_498_314),
  ("IxVMPerf.mul_row", 517_997_181),
  ("IxVMPerf.context_tower", 767_351_113),
  ("IxVMPerf.mul_wide", 358_716_905)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_081_389),
  ("IxVMPrim.nat_mul_lit", 369_637_843),
  ("IxVMPrim.nat_div_lit", 2_613_576_331),
  ("IxVMPrim.nat_land_lit", 8_704_371_718)]

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
             accept := true, expectedFftCost := some 137_022_371_636, witness := witness }

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
    return { c with expectedFftCost := some 449_390_693_488 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
