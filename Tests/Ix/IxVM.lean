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
  ("HEq", 194_744_126),
  ("HEq.rec", 201_865_366),
  ("Eq.rec", 200_214_225),
  ("Nat", 194_509_491),
  ("Nat.add", 252_498_309),
  ("Nat.add_comm", 440_393_996),
  ("Nat.decEq", 511_387_231),
  ("Nat.decLe", 1_031_114_234),
  ("Nat.sub_le_of_le_add", 2_261_397_231),
  ("Nat.shiftRight_succ", 382_335_827),
  ("Trans.mk", 205_027_311),
  ("Array.append_assoc", 10_846_508_833),
  ("Vector.append", 11_120_092_136),
  ("IxVMPrim.nat_add_lit", 245_349_695),
  ("IxVMPrim.nat_sub_lit", 245_385_003),
  ("IxVMPrim.nat_mul_lit", 218_641_381),
  ("IxVMPrim.nat_mul_big", 217_104_116),
  ("IxVMPrim.nat_div_lit", 223_691_365),
  ("IxVMPrim.nat_mod_lit", 223_889_253),
  ("IxVMPrim.nat_succ_lit", 215_391_266),
  ("IxVMPrim.nat_pred_lit", 218_369_364),
  ("IxVMPrim.nat_gcd_lit", 219_273_167),
  ("IxVMPrim.nat_land_lit", 216_377_971),
  ("IxVMPrim.nat_lor_lit", 217_955_185),
  ("IxVMPrim.nat_xor_lit", 219_310_099),
  ("IxVMPrim.nat_shl_lit", 219_344_424),
  ("IxVMPrim.nat_shr_lit", 219_496_672),
  ("IxVMPrim.nat_pow_big", 1_002_356_742),
  ("IxVMPrim.nat_beq_lit", 219_426_293),
  ("IxVMPrim.nat_ble_lit", 220_584_041),
  ("IxVMPrim.nat_cases_big", 242_260_907),
  ("IxVMPrim.nat_dec_le", 372_771_394),
  ("IxVMPrim.nat_dec_lt", 370_936_701),
  ("IxVMPrim.nat_dec_eq", 358_964_388),
  ("IxVMPrim.str_size_lit", 3_247_544_510),
  ("IxVMPrim.bv_to_nat_lit", 2_462_989_184),
  ("IxVMInd.Even", 239_161_025),
  ("IxVMInd.Odd", 239_167_529),
  ("IxVMInd.Even.rec", 262_741_383),
  ("IxVMInd.Odd.rec", 262_742_478),
  ("IxVMInd.IdxTeleN.rec", 238_536_704),
  ("IxVMInd.IdxTeleB.rec", 238_535_622),
  ("IxVMInd.SoloA.rec", 231_331_565),
  ("IxVMInd.SoloB.rec", 231_331_565),
  ("IxVMInd.UnsafeSquash", 197_599_977),
  ("IxVMInd.Tree", 197_083_440),
  ("IxVMInd.Tree.rec", 212_762_377),
  ("IxVMInd.DedupM", 201_616_180),
  ("IxVMInd.DedupM.rec", 222_291_023),
  ("IxVMInd.DepthM", 199_461_490),
  ("IxVMInd.DepthM.rec", 216_021_047),
  ("String.Internal.append", 2_892_343_005),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 3_210_192_678),
  ("Lean.Syntax.rec", 2_969_162_296),
  ("IxVMInd.AuxTie", 329_124_133),
  ("IxVMInd.AuxTie.rec", 386_701_953),
  ("IxVMInd.HiddenIdx", 196_163_213),
  ("IxVMInd.HiddenIdx.rec", 201_856_187),
  ("IxVMInd.thmMajorUse", 675_969_740),
  ("IxVMInd.partialKRec", 221_500_690),
  ("IxVMInd.deepRebase", 286_342_177),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_285_556_544),
  ("Lean.Widget.TaggedText.rec", 2_932_280_529),
  ("Lean.Doc.Part.rec", 2_989_965_195),
  ("Lean.Doc.Block.rec", 3_295_695_210),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 199_824_209),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 248_995_457),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 248_997_616),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 248_998_696),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 224_425_426),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 198_909_790),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 236_313_367),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 236_314_441),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 236_314_441),
  ("strOfListFoldSize", 3_255_194_698),
  ("strOfListFoldSizeAscii", 3_253_278_838),
  ("IxVMPrim.lazy_ble_offset", 251_243_223),
  ("IxVMPrim.lazy_unit_cast", 425_614_136),
  ("IxVMPrim.sizeof_unit", 236_307_530),
  ("IxVMPerf.let_continuations", 527_018_464),
  ("IxVMPerf.mul_row", 456_354_390),
  ("IxVMPerf.context_tower", 794_568_236),
  ("IxVMPerf.mul_wide", 318_932_504)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 222_606_535),
  ("IxVMPrim.nat_mul_lit", 327_959_515),
  ("IxVMPrim.nat_div_lit", 2_413_569_506),
  ("IxVMPrim.nat_land_lit", 8_444_323_814)]

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
             accept := true, expectedFftCost := some 130_860_906_335, witness := witness }

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
    return { c with expectedFftCost := some 438_941_726_961 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
