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

The legacy suite also pinned each claim's exact FFT cost. The formal program
has no such cost model (its circuits are sized by the trace plan), so only the
verdicts are pinned here.
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
def kernelCheckEntries : List String := [
  "HEq", "HEq.rec", "Eq.rec", "Nat", "Nat.add", "Nat.add_comm", "Nat.decEq", "Nat.decLe",
  "Nat.sub_le_of_le_add", "Nat.shiftRight_succ", "Trans.mk", "Array.append_assoc",
  "Vector.append",
  "IxVMPrim.nat_add_lit", "IxVMPrim.nat_sub_lit", "IxVMPrim.nat_mul_lit",
  "IxVMPrim.nat_mul_big", "IxVMPrim.nat_div_lit", "IxVMPrim.nat_mod_lit",
  "IxVMPrim.nat_succ_lit", "IxVMPrim.nat_pred_lit", "IxVMPrim.nat_gcd_lit",
  "IxVMPrim.nat_land_lit", "IxVMPrim.nat_lor_lit", "IxVMPrim.nat_xor_lit",
  "IxVMPrim.nat_shl_lit", "IxVMPrim.nat_shr_lit", "IxVMPrim.nat_pow_big",
  "IxVMPrim.nat_beq_lit", "IxVMPrim.nat_ble_lit", "IxVMPrim.nat_cases_big",
  "IxVMPrim.nat_dec_le", "IxVMPrim.nat_dec_lt", "IxVMPrim.nat_dec_eq",
  "IxVMPrim.str_size_lit", "IxVMPrim.bv_to_nat_lit",
  "IxVMInd.Even", "IxVMInd.Odd", "IxVMInd.Even.rec", "IxVMInd.Odd.rec",
  "IxVMInd.IdxTeleN.rec", "IxVMInd.IdxTeleB.rec", "IxVMInd.SoloA.rec", "IxVMInd.SoloB.rec",
  "IxVMInd.UnsafeSquash", "IxVMInd.Tree", "IxVMInd.Tree.rec", "IxVMInd.DedupM",
  "IxVMInd.DedupM.rec", "IxVMInd.DepthM", "IxVMInd.DepthM.rec",
  "String.Internal.append", "_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec",
  "Lean.Syntax.rec", "IxVMInd.AuxTie", "IxVMInd.AuxTie.rec", "IxVMInd.HiddenIdx",
  "IxVMInd.HiddenIdx.rec", "IxVMInd.thmMajorUse", "IxVMInd.partialKRec", "IxVMInd.deepRebase",
  "String.Slice.Pattern.Model.NoPrefixPatternModel.rec", "Lean.Widget.TaggedText.rec",
  "Lean.Doc.Part.rec", "Lean.Doc.Block.rec",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_1",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup1.A.rec_2",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedup2.A.rec_1",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_1",
  "_private.Tests.Ix.Compile.Mutual.0.Tests.Ix.Compile.Mutual.AuxDedupMixed.M.rec_2",
  "strOfListFoldSize", "strOfListFoldSizeAscii",
  "IxVMPrim.lazy_ble_offset", "IxVMPrim.lazy_unit_cast", "IxVMPrim.sizeof_unit",
  "IxVMPerf.let_continuations", "IxVMPerf.mul_row", "IxVMPerf.context_tower",
  "IxVMPerf.mul_wide"]

/-- Claims that validate the roles their proofs use (validator 3), one per
cost class: no operation, structural operations, `div`/`mod`/shifts, and
`gcd`/`land`/`lor`/`xor`. -/
def validatingCheckEntries : List String := [
  "IxVMPrim.nat_succ_lit", "IxVMPrim.nat_mul_lit", "IxVMPrim.nat_div_lit",
  "IxVMPrim.nat_land_lit"]

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
             accept := true, witness := witness }

/-- The verdict suite: every listed constant accepted, the binding claim of the
default table, and a shard of the shard pipeline. A listed constant missing
from the environment (a toolchain bump that renamed it) is a failure, not a
skip. -/
def kernelChecks (env : Lean.Environment) : IO UInt32 := do
  let names := (kernelCheckEntries ++ validatingCheckEntries).map nameOfString
  let missing := names.filter (!env.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-kernel-checks] not in the environment: {missing}"
    return 1
  let started ← IO.monoMsNow
  let ixonEnv ← loadSharedIxonEnv names.toArray env
  IO.println s!"[ixvm-kernel-checks] compiled the closures in {(← IO.monoMsNow) - started} ms"
  let assumed := kernelCheckEntries.map fun n => kernelCheckCase ixonEnv (nameOfString n) true
  let validating := validatingCheckEntries.map fun n =>
    kernelCheckCase ixonEnv (nameOfString n) false
  let binding : Builder := fun _ => do
    let ctx ← Ix.ClaimContext.ofEnv ixonEnv
    Case.ofClaim "binding claim for the default table" ixonEnv (.binding ctx.spec ctx.binding)
  let shard ← shardCase env
  runCases "ixvm-kernel-checks" (assumed ++ validating ++ [binding, shard]).toArray

end Tests.Ix.IxVM

end
