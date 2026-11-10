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
  ("HEq", 226_909_690),
  ("HEq.rec", 234_562_390),
  ("Eq.rec", 232_891_780),
  ("Nat", 226_663_553),
  ("Nat.add", 290_847_072),
  ("Nat.add_comm", 497_888_686),
  ("Nat.decEq", 576_314_214),
  ("Nat.decLe", 1_147_919_567),
  ("Nat.sub_le_of_le_add", 2_521_940_530),
  ("Nat.shiftRight_succ", 439_866_140),
  ("Trans.mk", 237_657_081),
  ("Array.append_assoc", 18_046_985_414),
  ("Vector.append", 18_353_098_877),
  ("IxVMPrim.nat_add_lit", 283_561_398),
  ("IxVMPrim.nat_sub_lit", 283_594_855),
  ("IxVMPrim.nat_mul_lit", 254_201_038),
  ("IxVMPrim.nat_mul_big", 252_500_441),
  ("IxVMPrim.nat_div_lit", 260_260_971),
  ("IxVMPrim.nat_mod_lit", 260_474_415),
  ("IxVMPrim.nat_succ_lit", 250_405_034),
  ("IxVMPrim.nat_pred_lit", 254_057_191),
  ("IxVMPrim.nat_gcd_lit", 254_814_532),
  ("IxVMPrim.nat_land_lit", 251_676_291),
  ("IxVMPrim.nat_lor_lit", 253_432_752),
  ("IxVMPrim.nat_xor_lit", 255_113_937),
  ("IxVMPrim.nat_shl_lit", 254_896_800),
  ("IxVMPrim.nat_shr_lit", 255_039_486),
  ("IxVMPrim.nat_pow_big", 1_033_370_705),
  ("IxVMPrim.nat_beq_lit", 255_220_916),
  ("IxVMPrim.nat_ble_lit", 256_504_502),
  ("IxVMPrim.nat_cases_big", 280_425_430),
  ("IxVMPrim.nat_dec_le", 424_048_768),
  ("IxVMPrim.nat_dec_lt", 421_136_954),
  ("IxVMPrim.nat_dec_eq", 409_176_435),
  ("IxVMPrim.str_size_lit", 3_593_491_394),
  ("IxVMPrim.bv_to_nat_lit", 2_726_696_651),
  ("IxVMInd.Even", 276_784_605),
  ("IxVMInd.Odd", 276_791_109),
  ("IxVMInd.Even.rec", 302_879_149),
  ("IxVMInd.Odd.rec", 302_881_340),
  ("IxVMInd.IdxTeleN.rec", 275_765_023),
  ("IxVMInd.IdxTeleB.rec", 275_763_941),
  ("IxVMInd.SoloA.rec", 267_972_732),
  ("IxVMInd.SoloB.rec", 267_972_732),
  ("IxVMInd.UnsafeSquash", 230_261_447),
  ("IxVMInd.Tree", 229_572_288),
  ("IxVMInd.Tree.rec", 246_813_886),
  ("IxVMInd.DedupM", 234_810_642),
  ("IxVMInd.DedupM.rec", 257_385_714),
  ("IxVMInd.DepthM", 232_314_663),
  ("IxVMInd.DepthM.rec", 250_443_655),
  ("String.Internal.append", 3_201_855_517),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_553_942_784),
  ("Lean.Syntax.rec", 3_285_779_591),
  ("IxVMInd.AuxTie", 378_775_218),
  ("IxVMInd.AuxTie.rec", 441_097_915),
  ("IxVMInd.HiddenIdx", 228_541_834),
  ("IxVMInd.HiddenIdx.rec", 234_738_510),
  ("IxVMInd.thmMajorUse", 757_162_832),
  ("IxVMInd.partialKRec", 256_899_132),
  ("IxVMInd.deepRebase", 329_921_927),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_635_552_374),
  ("Lean.Widget.TaggedText.rec", 3_244_603_605),
  ("Lean.Doc.Part.rec", 3_306_813_430),
  ("Lean.Doc.Block.rec", 3_642_703_701),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 232_588_303),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 285_956_749),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 285_958_910),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 285_959_991),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 259_657_238),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 231_572_422),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 272_265_666),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 272_267_816),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 272_267_816),
  ("strOfListFoldSize", 3_602_020_632),
  ("strOfListFoldSizeAscii", 3_600_148_274),
  ("IxVMPrim.lazy_ble_offset", 290_940_021),
  ("IxVMPrim.lazy_unit_cast", 483_979_498),
  ("IxVMPrim.sizeof_unit", 274_239_986),
  ("IxVMPerf.let_continuations", 563_260_658),
  ("IxVMPerf.mul_row", 517_031_823),
  ("IxVMPerf.context_tower", 866_619_215),
  ("IxVMPerf.mul_wide", 358_502_709)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 258_225_733),
  ("IxVMPrim.nat_mul_lit", 371_439_992),
  ("IxVMPrim.nat_div_lit", 2_664_881_338),
  ("IxVMPrim.nat_land_lit", 10_042_021_445)]

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
             accept := true, expectedFftCost := some 194_505_867_009, witness := witness }

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
    return { c with expectedFftCost := some 1_066_772_620_558 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
