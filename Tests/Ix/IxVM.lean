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
  ("HEq", 226_919_010),
  ("HEq.rec", 234_579_501),
  ("Eq.rec", 232_903_913),
  ("Nat", 226_672_583),
  ("Nat.add", 290_809_222),
  ("Nat.add_comm", 498_990_932),
  ("Nat.decEq", 576_798_190),
  ("Nat.decLe", 1_176_679_594),
  ("Nat.sub_le_of_le_add", 2_573_211_804),
  ("Nat.shiftRight_succ", 440_118_041),
  ("Trans.mk", 237_833_321),
  ("Array.append_assoc", 18_445_644_364),
  ("Vector.append", 18_751_854_207),
  ("IxVMPrim.nat_add_lit", 283_665_035),
  ("IxVMPrim.nat_sub_lit", 283_698_493),
  ("IxVMPrim.nat_mul_lit", 254_242_816),
  ("IxVMPrim.nat_mul_big", 252_540_230),
  ("IxVMPrim.nat_div_lit", 260_300_885),
  ("IxVMPrim.nat_mod_lit", 260_514_329),
  ("IxVMPrim.nat_succ_lit", 250_443_433),
  ("IxVMPrim.nat_pred_lit", 254_096_484),
  ("IxVMPrim.nat_gcd_lit", 254_852_573),
  ("IxVMPrim.nat_land_lit", 251_723_352),
  ("IxVMPrim.nat_lor_lit", 253_474_520),
  ("IxVMPrim.nat_xor_lit", 255_155_730),
  ("IxVMPrim.nat_shl_lit", 254_935_413),
  ("IxVMPrim.nat_shr_lit", 255_076_578),
  ("IxVMPrim.nat_pow_big", 1_033_644_579),
  ("IxVMPrim.nat_beq_lit", 255_278_288),
  ("IxVMPrim.nat_ble_lit", 256_564_047),
  ("IxVMPrim.nat_cases_big", 280_429_076),
  ("IxVMPrim.nat_dec_le", 423_817_323),
  ("IxVMPrim.nat_dec_lt", 420_910_076),
  ("IxVMPrim.nat_dec_eq", 408_916_816),
  ("IxVMPrim.str_size_lit", 3_632_759_254),
  ("IxVMPrim.bv_to_nat_lit", 2_770_554_008),
  ("IxVMInd.Even", 276_914_486),
  ("IxVMInd.Odd", 276_920_991),
  ("IxVMInd.Even.rec", 303_025_867),
  ("IxVMInd.Odd.rec", 303_028_058),
  ("IxVMInd.IdxTeleN.rec", 275_846_473),
  ("IxVMInd.IdxTeleB.rec", 275_845_391),
  ("IxVMInd.SoloA.rec", 268_045_489),
  ("IxVMInd.SoloB.rec", 268_045_489),
  ("IxVMInd.Tree", 229_592_632),
  ("IxVMInd.Tree.rec", 246_856_227),
  ("IxVMInd.DedupM", 234_841_665),
  ("IxVMInd.DedupM.rec", 257_435_445),
  ("IxVMInd.DepthM", 232_336_805),
  ("IxVMInd.DepthM.rec", 250_492_812),
  ("String.Internal.append", 3_241_781_234),
  ("Lean.Syntax.rec", 3_325_958_902),
  ("IxVMInd.AuxTie", 379_195_395),
  ("IxVMInd.AuxTie.rec", 441_548_223),
  ("IxVMInd.HiddenIdx", 228_551_853),
  ("IxVMInd.HiddenIdx.rec", 234_752_786),
  ("IxVMInd.thmMajorUse", 774_365_991),
  ("IxVMInd.partialKRec", 256_939_721),
  ("IxVMInd.deepRebase", 329_980_401),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_674_897_822),
  ("Lean.Widget.TaggedText.rec", 3_284_619_923),
  ("Lean.Doc.Part.rec", 3_347_116_243),
  ("Lean.Doc.Block.rec", 3_682_721_674),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 232_630_564),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 286_010_023),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 286_012_184),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 286_013_264),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 259_720_490),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 231_605_556),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 272_318_803),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 272_320_953),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 272_320_953),
  ("strOfListFoldSize", 3_641_453_750),
  ("strOfListFoldSizeAscii", 3_639_457_997),
  ("IxVMPrim.lazy_ble_offset", 291_056_070),
  ("IxVMPrim.lazy_unit_cast", 483_847_158),
  ("IxVMPrim.sizeof_unit", 274_290_287),
  ("IxVMPerf.let_continuations", 287_606_397),
  ("IxVMPerf.mul_row", 518_102_559),
  ("IxVMPerf.context_tower", 776_235_534),
  ("IxVMPerf.mul_wide", 358_796_574)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_288_224),
  ("IxVMPrim.nat_mul_lit", 370_719_515),
  ("IxVMPrim.nat_div_lit", 2_714_480_871),
  ("IxVMPrim.nat_land_lit", 10_100_339_404)]

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
             accept := true, expectedFftCost := some 195_481_912_697, witness := witness }

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
    return { c with expectedFftCost := some 1_068_164_743_063 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
