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
  ("HEq", 232_623_386),
  ("HEq.rec", 240_270_439),
  ("Eq.rec", 238_626_301),
  ("Nat", 232_373_009),
  ("Nat.add", 296_756_977),
  ("Nat.add_comm", 505_777_347),
  ("Nat.decEq", 583_591_922),
  ("Nat.decLe", 1_185_546_700),
  ("Nat.sub_le_of_le_add", 2_583_419_004),
  ("Nat.shiftRight_succ", 446_883_475),
  ("Trans.mk", 243_732_414),
  ("Array.append_assoc", 19_934_782_897),
  ("Vector.append", 20_244_360_312),
  ("IxVMPrim.nat_add_lit", 289_881_498),
  ("IxVMPrim.nat_sub_lit", 289_916_292),
  ("IxVMPrim.nat_mul_lit", 260_107_458),
  ("IxVMPrim.nat_mul_big", 258_397_351),
  ("IxVMPrim.nat_div_lit", 266_176_353),
  ("IxVMPrim.nat_mod_lit", 266_393_587),
  ("IxVMPrim.nat_succ_lit", 256_295_811),
  ("IxVMPrim.nat_pred_lit", 259_961_576),
  ("IxVMPrim.nat_gcd_lit", 260_715_938),
  ("IxVMPrim.nat_land_lit", 257_575_596),
  ("IxVMPrim.nat_lor_lit", 259_334_886),
  ("IxVMPrim.nat_xor_lit", 261_020_580),
  ("IxVMPrim.nat_shl_lit", 260_799_352),
  ("IxVMPrim.nat_shr_lit", 260_986_165),
  ("IxVMPrim.nat_pow_big", 1_040_312_211),
  ("IxVMPrim.nat_beq_lit", 261_185_905),
  ("IxVMPrim.nat_ble_lit", 262_468_981),
  ("IxVMPrim.nat_cases_big", 286_426_419),
  ("IxVMPrim.nat_dec_le", 430_759_507),
  ("IxVMPrim.nat_dec_lt", 427_793_314),
  ("IxVMPrim.nat_dec_eq", 415_520_840),
  ("IxVMPrim.str_size_lit", 3_647_608_206),
  ("IxVMPrim.bv_to_nat_lit", 2_782_015_358),
  ("IxVMInd.Even", 550_628_496),
  ("IxVMInd.Odd", 550_620_292),
  ("IxVMInd.Even.rec", 554_713_267),
  ("IxVMInd.Odd.rec", 554_717_955),
  ("IxVMInd.IdxTeleN.rec", 530_778_772),
  ("IxVMInd.IdxTeleB.rec", 530_775_267),
  ("IxVMInd.SoloA.rec", 433_641_237),
  ("IxVMInd.SoloB.rec", 433_640_091),
  ("IxVMInd.Tree", 696_582_093),
  ("IxVMInd.Tree.rec", 698_868_724),
  ("IxVMInd.DedupM", 873_618_625),
  ("IxVMInd.DedupM.rec", 877_240_924),
  ("IxVMInd.DepthM", 854_482_503),
  ("IxVMInd.DepthM.rec", 856_843_868),
  ("String.Internal.append", 3_256_023_205),
  ("Lean.Syntax.rec", 4_623_268_966),
  ("IxVMInd.AuxTie", 1_676_144_829),
  ("IxVMInd.AuxTie.rec", 1_686_887_866),
  ("IxVMInd.HiddenIdx", 234_270_616),
  ("IxVMInd.HiddenIdx.rec", 240_538_703),
  ("IxVMInd.thmMajorUse", 782_357_596),
  ("IxVMInd.partialKRec", 262_804_401),
  ("IxVMInd.deepRebase", 336_355_626),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_681_831_310),
  ("Lean.Widget.TaggedText.rec", 4_896_728_096),
  ("Lean.Doc.Part.rec", 24_182_504_183),
  ("Lean.Doc.Block.rec", 21_379_738_645),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 1_550_757_036),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 1_562_441_506),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 1_562_444_810),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 1_562_442_286),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 871_720_377),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 1_380_481_636),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 1_387_968_393),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 1_387_969_646),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 1_387_970_899),
  ("strOfListFoldSize", 3_656_295_374),
  ("strOfListFoldSizeAscii", 3_654_288_705),
  ("IxVMPrim.lazy_ble_offset", 297_340_658),
  ("IxVMPrim.lazy_unit_cast", 491_122_135),
  ("IxVMPrim.sizeof_unit", 280_409_089),
  ("IxVMPerf.let_continuations", 293_336_356),
  ("IxVMPerf.mul_row", 524_040_397),
  ("IxVMPerf.context_tower", 781_623_012),
  ("IxVMPerf.mul_wide", 364_338_422)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 264_265_958),
  ("IxVMPrim.nat_mul_lit", 377_081_133),
  ("IxVMPrim.nat_div_lit", 2_724_797_978),
  ("IxVMPrim.nat_land_lit", 10_115_331_681)]

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
             accept := true, expectedFftCost := some 197_268_675_776, witness := witness }

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
    return { c with expectedFftCost := some 1_070_159_487_520 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
