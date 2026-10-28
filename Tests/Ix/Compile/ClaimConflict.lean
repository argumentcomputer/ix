/-
  compile-claim-conflict: single ownership of compiled names, in both
  compilers (a name assigned twice is an error unless both assignments are
  equal).

  Rust's scheduler claims names insert-once (`CompileState::claim_compiled_name`)
  and raises
  `conflicting claims for name '…': already registered at …, claimed again at …`
  on a second claim at another address. The Lean drivers check the same claims
  at merge time (`Ix.CompileM.checkBlockClaims`). Two parts:

  1. **Driver API.** The insert-once merge is driven directly: through
     `checkBlockClaims` then `mergeCompiledBlock` (what every driver does
     with a compiled block) and through `applyAuxBlockOutcome` (the wave
     driver's merge, with two blocks of one wave claiming one name): a second
     compiled claim at another address is refused with Rust's message,
     character for character, and an identical re-claim is accepted. An
     identical re-claim of a name an earlier block owns keeps the owner's
     `Named` entry, while a block's own second registration of a name
     replaces its first. A source dependency is ready only when its own block
     has settled (`auxDependencyReady`).
  2. **Both compilers.** A constructed closure holds a user constant named
     `T.below` (a plain definition, not Lean's auxiliary) for a recursive
     inductive `T` whose field type depends on it, so `T.below` compiles
     before `T` in every schedule. Real Lean input cannot contain this:
     Lean's own `mkBelow` would have failed on the name. Both compilers
     compile Lean's declarations as given, so `T`'s block claims only its
     own names and nothing claims the user's `T.below` a second time: the
     Rust compiler (`ix compile`'s FFI), the fold, the reference schedule
     (least and greatest key first) and the `ix compile-lean` pipeline (1, 4,
     16 workers) must all compile the whole closure, with no refusal.

  Run with: `lake test -- --ignored compile-claim-conflict`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.CompileDriver
import Tests.Ix.Compile.ScheduleReference

open Lean

namespace Tests.Ix.Compile.ClaimConflict

namespace Fixture

/-- Stands in for a user constant named `T.below`: the constructed closure
    renames it. -/
def FakeBelow : Type := PUnit

/-- `T`'s field type. In the constructed closure its body is the user
    `T.below`, so `T`'s block depends on it. -/
def Dep : Type := FakeBelow

/-- A recursive inductive: Lean generates `T.below` for it. -/
inductive T where
  | leaf : T
  | node : Dep → T → T

end Fixture

/-! ## Part 1: the driver API -/

section DriverApi
open Ix.CompileM

private def addr (s : String) : Address := Address.blake3 s.toUTF8

private def ixName (s : String) : Ix.Name := Ix.Name.fromLeanName s.toName

/-- Rust's `name_claim_conflict` format, written out. -/
private def rustConflict (n : Ix.Name) (existing claimed : Address) : String :=
  s!"conflicting claims for name '{n.pretty}': already registered at \
{(toString existing).take 12}, claimed again at {(toString claimed).take 12}"

private def emptyAcc : DriverAcc := { cenv := default }

/-- A block result whose lone constant `lo` sits at `a` (no projections). -/
private def loneResult (a : Address) : BlockResult :=
  { block := default, blockBytes := ByteArray.empty, blockAddr := a }

/-- What every driver does with a compiled block: `checkBlockClaims`, then
    `mergeCompiledBlock` if the check passes. -/
private def merge (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult) (cache : BlockState) :
    Except CompileError DriverAcc := do
  checkBlockClaims acc.cenv (primaryClaims lo result)
  pure (mergeCompiledBlock acc lo result cache)

private def errOf : Except CompileError DriverAcc → Option String
  | .error (.invalidMutualBlock r) => some r
  | .error e => some s!"(another error) {e}"
  | .ok _ => none

/-- The driver-API cases: (label, expected message or `none` for accepted,
    actual). -/
def driverCases : List (String × Option String × Option String) := Id.run do
  let n := ixName "Fx.T.below"
  let x := addr "x"
  let y := addr "y"
  let withCompiled : DriverAcc :=
    { cenv := { (default : CompileEnv) with nameToAddr := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName _).insert n x } }
  let mut cases : List (String × Option String × Option String) := []
  -- a second compiled claim at another address
  cases := cases ++ [("second compiled claim", some (rustConflict n x y),
    errOf (merge withCompiled n (loneResult y) default))]
  cases := cases ++ [("identical second compiled claim", none,
    errOf (merge withCompiled n (loneResult x) default))]
  -- the wave driver: two blocks of one wave, computed on one snapshot,
  -- claim `n` at different addresses; the second merge is refused and the
  -- block is reported failed (its dependents are released as failed)
  let all : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert n
  let (acc₁, _, failed₁) := applyAuxBlockOutcome emptyAcc n all
    (.compiled (loneResult x) default)
  let (acc₂, names₂, failed₂) := applyAuxBlockOutcome acc₁ n all
    (.compiled (loneResult y) default)
  let waveMsg : Option String :=
    if failed₁ || !failed₂ || !names₂.isEmpty || acc₂.cenv.nameToAddr.get? n != some x then
      some s!"wrong outcome: failed {failed₁}/{failed₂}, registered {names₂.size}, \
claim {acc₂.cenv.nameToAddr.get? n}"
    else (acc₂.cenv.ungrounded.get? n).map fun m => (m.drop "invalidMutualBlock: ".length).toString
  cases := cases ++ [("wave: two blocks of one wave", some (rustConflict n x y), waveMsg)]
  return cases

/-- An identical re-claim of a name an earlier block owns does not replace
    the owner's `Named` entry (its metadata, its hints); a name one block
    registers twice keeps that block's last entry. Mirrors Rust
    `compile::tests::identical_reclaim_keeps_the_owner_named` and
    `reclaim_within_one_block_reregisters`. -/
def ownerNamedCheck : Except String Unit := do
  let n := ixName "Fx.A.rec_1"
  let lo := ixName "Fx.T"
  let x := addr "x"
  let tag (s : String) : Ixon.ConstantMeta := .new (.muts #[#[addr s]] none)
  let owner : Ixon.Named :=
    { addr := x, constMeta := tag "owner", hints := some .abbrev }
  -- a primary name over an earlier block's compiled claim of `n` at `x`
  let compiled : DriverAcc := { cenv := { (default : CompileEnv) with
    nameToAddr := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName _).insert n x
    nameToNamed := ({} : Std.HashMap _ _).insert n owner } }
  let acc ← (merge compiled n { loneResult x with blockMeta := tag "later" } default).mapError toString
  if acc.cenv.nameToNamed.get? n != some owner then
    throw "an identical primary re-claim replaced the owner's Named"
  -- one block registering `n` twice keeps its own last entry
  let twice : BlockState :=
    { (default : BlockState) with
      mutsNamed := #[(n, { addr := x, constMeta := tag "first" }),
        (n, { addr := x, constMeta := tag "second" })] }
  let acc ← (merge emptyAcc lo (loneResult (addr "t")) twice).mapError toString
  if (acc.cenv.nameToNamed.get? n).map (·.constMeta) != some (tag "second") then
    throw "a block's own second registration was dropped"

/-- The one readiness rule: a source-owned name is ready only when its own
    block has settled, even when the state already resolves it; a name no
    block owns is ready once it resolves. -/
def readinessCases : List (String × Bool) :=
  let a := ixName "Fx.Ready.a"
  let other := ixName "Fx.Ready.other"
  let canonical := addr "ready-canonical"
  let all : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert a
  let cenv : CompileEnv := { (default : CompileEnv) with
    nameToAddr := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName _).insert a canonical
      |>.insert other canonical }
  let sourceOwned := fun n => all.contains n
  [("source dependency waits despite resolution",
    !auxDependencyReady sourceOwned cenv {} a &&
    auxDependencyReady sourceOwned cenv all a &&
    auxDependencyReady sourceOwned cenv {} other &&
    !auxDependencyReady sourceOwned cenv {} (ixName "Fx.Ready.absent"))]

end DriverApi

/-! ## Part 2: both compilers on a constructed closure -/

def tName : Name := ``Fixture.T
def belowName : Name := tName ++ `below

/-- The closure of `T`, `T.rec` and `Dep`, with `FakeBelow` renamed to
    `T.below` and `Dep`'s body pointing at it. Lean's own auxiliaries of `T`
    are not in it: nothing in the closure references them. -/
def conflictClosure (env : Environment) : Except String (List (Name × ConstantInfo)) := do
  let some (.defnInfo fv) := env.find? ``Fixture.FakeBelow | throw "FakeBelow missing"
  let some (.defnInfo dv) := env.find? ``Fixture.Dep | throw "Dep missing"
  if (dv.value.getUsedConstants.contains ``Fixture.FakeBelow) == false then
    throw "Dep does not mention FakeBelow"
  let base := Ix.EnvScope.collectDeps env [``Fixture.Dep, tName, tName ++ `rec]
  let userBelow : ConstantInfo := .defnInfo { fv with name := belowName, all := [belowName] }
  let dep' : ConstantInfo := .defnInfo { dv with value := .const belowName [] }
  let rest := base.filterMap fun (n, ci) =>
    if n == ``Fixture.FakeBelow then none
    else if n == ``Fixture.Dep then some (n, dep')
    else some (n, ci)
  return (belowName, userBelow) :: rest

/-- The `ix compile-lean` pipeline on a closure (`compileInputFromEnv`, then
    `compileLeanInput`). -/
def leanCompile (env : Environment) (closure : List (Name × ConstantInfo)) (workers : Nat) :
    IO Ix.CompileM.LeanPipelineOut := do
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv env closure).mapError toString)
  match ← Ix.CompileM.compileLeanInput input (numWorkers := workers) with
  | .ok o => pure o
  | .error e => throw (IO.userError s!"Lean compile failed: {e}")

def run : IO UInt32 := do
  let mut failures := 0
  match ownerNamedCheck with
  | .ok () => IO.println "[claim-conflict] owner Named: an identical re-claim keeps the \
owner's entry; a block's own re-registration wins"
  | .error e =>
    failures := failures + 1
    IO.println s!"[claim-conflict] owner Named: FAIL: {e}"
  -- Part 1
  for (label, expected, actual) in driverCases do
    if expected == actual then
      IO.println s!"[claim-conflict] driver: {label}: {actual.getD "accepted"}"
    else
      failures := failures + 1
      IO.println s!"[claim-conflict] driver: {label}: FAIL: expected {expected.getD "accepted"}, \
got {actual.getD "accepted"}"
  for (label, passed) in readinessCases do
    if passed then
      IO.println s!"[claim-conflict] readiness: {label}: PASS"
    else
      failures := failures + 1
      IO.println s!"[claim-conflict] readiness: {label}: FAIL"
  -- Part 2
  let env ← get_env!
  let closure ← IO.ofExcept (conflictClosure env)
  IO.println s!"[claim-conflict] constructed closure: {closure.length} constants"
  -- Rust (the `ix compile` FFI), partial output allowed so the status
  -- lists every refused constant
  let dir ← IO.FS.createTempDir
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env closure)
  let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared (dir / "rs.ixe").toString true
  IO.FS.removeDirAll dir
  for (n, m) in status.ungrounded.toList do
    failures := failures + 1
    IO.println s!"[claim-conflict] FAIL: rust refuses {n}: {m}"
  -- Lean: every schedule
  let mut runs : Array (String × List (String × String)) := #[]
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  match Ix.CompileM.compileEnvFold phases.rawEnv phases.condensed with
  | .error e => throw (IO.userError s!"[claim-conflict] fold: {e}")
  | .ok (_, _, cenv) =>
    runs := runs.push ("fold", cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
  -- the test-only reference schedule, with the least and with the greatest
  -- ready key first
  for least in [true, false] do
    match ScheduleReference.sequential phases.rawEnv phases.condensed (least := least) with
    | .error e => throw (IO.userError s!"[claim-conflict] reference schedule: {e}")
    | .ok (_, _, cenv) =>
      runs := runs.push (s!"reference, {if least then "least" else "greatest"} key first",
        cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
  for k in [1, 4, 16] do
    let out ← leanCompile env closure k
    runs := runs.push (s!"compile-lean --workers {k}",
      out.cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
  for (label, refusals) in runs do
    if refusals.isEmpty then
      IO.println s!"[claim-conflict] {label}: the whole closure compiles, as in Rust"
    else
      failures := failures + 1
      IO.println s!"[claim-conflict] {label}: FAIL: {refusals.length} refusal(s)"
      for (n, m) in refusals do
        IO.println s!"[claim-conflict]   lean {n}: {m}"
  IO.println s!"[claim-conflict] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ClaimConflict
