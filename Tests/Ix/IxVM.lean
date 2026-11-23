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
  ("HEq", 150_236_866),
  ("HEq.rec", 153_909_488),
  ("Eq.rec", 152_804_798),
  ("Nat", 150_174_227),
  ("Nat.add", 184_637_667),
  ("Nat.add_comm", 294_906_875),
  ("Nat.decEq", 338_018_674),
  ("Nat.decLe", 652_423_002),
  ("Nat.sub_le_of_le_add", 1_372_096_222),
  ("Nat.shiftRight_succ", 265_755_546),
  ("Trans.mk", 157_033_818),
  ("Array.append_assoc", 7_116_743_023),
  ("Vector.append", 7_269_380_232),
  ("IxVMPrim.nat_add_lit", 179_414_951),
  ("IxVMPrim.nat_sub_lit", 179_421_750),
  ("IxVMPrim.nat_mul_lit", 163_373_053),
  ("IxVMPrim.nat_mul_big", 162_536_118),
  ("IxVMPrim.nat_div_lit", 165_894_683),
  ("IxVMPrim.nat_mod_lit", 166_053_454),
  ("IxVMPrim.nat_succ_lit", 161_522_290),
  ("IxVMPrim.nat_pred_lit", 163_286_334),
  ("IxVMPrim.nat_gcd_lit", 163_609_344),
  ("IxVMPrim.nat_land_lit", 162_161_297),
  ("IxVMPrim.nat_lor_lit", 162_929_044),
  ("IxVMPrim.nat_xor_lit", 163_652_282),
  ("IxVMPrim.nat_shl_lit", 163_650_896),
  ("IxVMPrim.nat_shr_lit", 163_712_731),
  ("IxVMPrim.nat_pow_big", 209_274_553),
  ("IxVMPrim.nat_beq_lit", 163_754_435),
  ("IxVMPrim.nat_ble_lit", 164_433_453),
  ("IxVMPrim.nat_cases_big", 178_413_734),
  ("IxVMPrim.nat_dec_le", 209_792_232),
  ("IxVMPrim.nat_dec_lt", 216_289_504),
  ("IxVMPrim.nat_dec_eq", 191_649_448),
  ("IxVMPrim.str_size_lit", 1_709_513_274),
  ("IxVMPrim.bv_to_nat_lit", 1_454_996_557),
  ("IxVMInd.Even", 292_534_866),
  ("IxVMInd.Odd", 292_534_866),
  ("IxVMInd.Even.rec", 292_889_493),
  ("IxVMInd.Odd.rec", 292_889_493),
  ("IxVMInd.IdxTeleN.rec", 284_989_462),
  ("IxVMInd.IdxTeleB.rec", 284_989_462),
  ("IxVMInd.SoloA.rec", 246_267_720),
  ("IxVMInd.SoloB.rec", 246_267_720),
  ("IxVMInd.Tree", 361_717_805),
  ("IxVMInd.Tree.rec", 362_035_309),
  ("IxVMInd.DedupM", 434_274_665),
  ("IxVMInd.DedupM.rec", 434_607_509),
  ("IxVMInd.DepthM", 435_580_643),
  ("IxVMInd.DepthM.rec", 435_864_347),
  ("String.Internal.append", 1_718_913_556),
  ("Lean.Syntax.rec", 770_900_218),
  ("IxVMInd.AuxTie", 736_984_047),
  ("IxVMInd.AuxTie.rec", 737_567_020),
  ("IxVMInd.HiddenIdx", 151_086_281),
  ("IxVMInd.HiddenIdx.rec", 154_105_418),
  ("IxVMInd.NestParIdx.rec", 530_104_570),
  ("IxVMInd.NestListIdx.rec", 498_874_637),
  ("IxVMInd.NestRefl.rec", 396_312_338),
  ("IxVMInd.NestReflOpt.rec", 353_277_612),
  ("IxVMInd.thmMajorUse", 433_376_148),
  ("IxVMInd.partialKRec", 165_068_681),
  ("IxVMInd.deepRebase", 205_414_867),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 1_733_867_130),
  ("Lean.Widget.TaggedText.rec", 871_613_654),
  ("Lean.Doc.Part.rec", 8_125_320_653),
  ("Lean.Doc.Block.rec", 6_872_627_698),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 714_732_378),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 715_342_223),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 715_338_406),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 715_338_406),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 439_259_968),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 632_890_648),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 633_362_842),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 633_362_842),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 633_362_842),
  ("strOfListFoldSize", 172_123_877),
  ("strOfListFoldSizeAscii", 172_112_242),
  ("IxVMPrim.lazy_ble_offset", 182_951_617),
  ("IxVMPrim.lazy_unit_cast", 292_385_401),
  ("IxVMPrim.sizeof_unit", 173_957_472),
  ("IxVMPerf.let_continuations", 297_626_467),
  ("IxVMPerf.mul_row", 275_994_705),
  ("IxVMPerf.context_tower", 539_161_760),
  ("IxVMPerf.mul_wide", 202_922_722)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 166_699_307),
  ("IxVMPrim.nat_mul_lit", 227_174_508),
  ("IxVMPrim.nat_div_lit", 1_427_008_980),
  ("IxVMPrim.nat_land_lit", 4_331_963_941)]

/-- Constants of `Tests.Ix.Kernel.EntryCaseDefs`, loaded at run time (some of
its blocks are declared through Lean's kernel, which the fixtures module
cannot export), with claims that assume their binding. -/
def entryCheckEntries : List (String × Nat) := [
  ("Tests.Ix.Kernel.EntryCaseDefs.BD1.rec", 378_902_075),
  ("Tests.Ix.Kernel.EntryCaseDefs.BD2.rec", 379_464_974),
  ("Tests.Ix.Kernel.EntryCaseDefs.EA.rec", 533_925_981)]

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
             accept := true, expectedFftCost := some 72_096_916_275, witness := witness }

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
    return { c with expectedFftCost := some 233_027_783_556 }
  let shard ← shardCase env
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (entryCheckEntries.map (nameOfString ∘ Prod.fst)).toArray fenv
  let entry := entryCheckEntries.map fun (n, cost) => fun u => do
    let c ← kernelCheckCase fixEnv (nameOfString n) true u
    return { c with expectedFftCost := some cost }
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ entry ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
