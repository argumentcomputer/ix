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
  ("HEq", 181_222_276),
  ("HEq.rec", 187_949_003),
  ("Eq.rec", 186_309_677),
  ("Nat", 180_996_493),
  ("Nat.add", 234_150_196),
  ("Nat.add_comm", 406_393_175),
  ("Nat.decEq", 475_224_904),
  ("Nat.decLe", 955_838_855),
  ("Nat.sub_le_of_le_add", 2_091_598_646),
  ("Nat.shiftRight_succ", 348_062_225),
  ("Trans.mk", 191_118_045),
  ("Array.append_assoc", 10_219_505_901),
  ("Vector.append", 10_471_313_435),
  ("IxVMPrim.nat_add_lit", 228_090_740),
  ("IxVMPrim.nat_sub_lit", 228_130_761),
  ("IxVMPrim.nat_mul_lit", 202_995_817),
  ("IxVMPrim.nat_mul_big", 201_617_450),
  ("IxVMPrim.nat_div_lit", 207_069_990),
  ("IxVMPrim.nat_mod_lit", 207_260_146),
  ("IxVMPrim.nat_succ_lit", 200_275_145),
  ("IxVMPrim.nat_pred_lit", 202_690_128),
  ("IxVMPrim.nat_gcd_lit", 203_625_797),
  ("IxVMPrim.nat_land_lit", 201_060_336),
  ("IxVMPrim.nat_lor_lit", 202_472_994),
  ("IxVMPrim.nat_xor_lit", 203_449_308),
  ("IxVMPrim.nat_shl_lit", 203_698_701),
  ("IxVMPrim.nat_shr_lit", 203_849_589),
  ("IxVMPrim.nat_pow_big", 982_288_376),
  ("IxVMPrim.nat_beq_lit", 203_750_325),
  ("IxVMPrim.nat_ble_lit", 204_903_195),
  ("IxVMPrim.nat_cases_big", 224_581_117),
  ("IxVMPrim.nat_dec_le", 344_205_949),
  ("IxVMPrim.nat_dec_lt", 343_153_037),
  ("IxVMPrim.nat_dec_eq", 331_339_321),
  ("IxVMPrim.str_size_lit", 2_987_966_127),
  ("IxVMPrim.bv_to_nat_lit", 2_273_661_783),
  ("IxVMInd.Even", 222_296_008),
  ("IxVMInd.Odd", 222_297_039),
  ("IxVMInd.Even.rec", 243_926_626),
  ("IxVMInd.Odd.rec", 243_925_584),
  ("IxVMInd.IdxTeleN.rec", 221_676_518),
  ("IxVMInd.IdxTeleB.rec", 221_676_518),
  ("IxVMInd.SoloA.rec", 214_871_036),
  ("IxVMInd.SoloB.rec", 214_871_036),
  ("IxVMInd.UnsafeSquash", 183_884_473),
  ("IxVMInd.Tree", 183_518_760),
  ("IxVMInd.Tree.rec", 198_196_233),
  ("IxVMInd.DedupM", 187_698_641),
  ("IxVMInd.DedupM.rec", 207_000_492),
  ("IxVMInd.DepthM", 185_729_570),
  ("IxVMInd.DepthM.rec", 201_293_968),
  ("String.Internal.append", 2_668_379_772),
  ("_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec", 2_956_396_990),
  ("Lean.Syntax.rec", 2_739_889_433),
  ("IxVMInd.AuxTie", 304_738_259),
  ("IxVMInd.AuxTie.rec", 358_957_907),
  ("IxVMInd.HiddenIdx", 182_480_784),
  ("IxVMInd.HiddenIdx.rec", 187_784_770),
  ("IxVMInd.thmMajorUse", 630_664_733),
  ("IxVMInd.partialKRec", 205_767_082),
  ("IxVMInd.deepRebase", 264_133_655),
  ("String.Slice.Pattern.Model.NoPrefixPatternModel.rec", 3_022_678_177),
  ("Lean.Widget.TaggedText.rec", 2_705_973_083),
  ("Lean.Doc.Part.rec", 2_760_884_954),
  ("Lean.Doc.Block.rec", 3_052_412_943),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A", 186_075_800),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec", 232_073_829),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1", 232_074_852),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2", 232_074_852),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1", 209_079_303),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M", 185_175_464),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec", 220_205_723),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1", 220_204_706),
  ("_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2", 220_204_706),
  ("strOfListFoldSize", 2_994_757_394),
  ("strOfListFoldSizeAscii", 2_992_999_348),
  ("IxVMPrim.lazy_ble_offset", 232_818_529),
  ("IxVMPrim.lazy_unit_cast", 392_016_875),
  ("IxVMPrim.sizeof_unit", 219_256_911),
  ("IxVMPerf.let_continuations", 509_834_930),
  ("IxVMPerf.mul_row", 414_432_709),
  ("IxVMPerf.context_tower", 757_985_429),
  ("IxVMPerf.mul_wide", 300_064_160)]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List (String × Nat) := [
  ("IxVMPrim.nat_succ_lit", 207_095_963),
  ("IxVMPrim.nat_mul_lit", 305_617_263),
  ("IxVMPrim.nat_div_lit", 2_255_564_708),
  ("IxVMPrim.nat_land_lit", 7_981_101_445)]

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
             accept := true, expectedFftCost := some 122_591_762_305, witness := witness }

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
    return { c with expectedFftCost := some 420_226_998_141 }
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
