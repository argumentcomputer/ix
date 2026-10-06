/-
  compile-claim-conflict: single ownership of compiled names, in both
  compilers (A0 report §6 item 4; Phase A §6 A7; design document §6.2, "a
  name assigned twice is an error unless both assignments are equal").

  Rust's scheduler claims names insert-once (`CompileState::claim_compiled_name`
  and `claim_aux_name`, compile.rs:324-370) and raises
  `conflicting claims for name '…': already registered at …, claimed again at …`
  on a second claim at another address. The Lean drivers check the same claims
  at merge time (`Ix.CompileM.checkBlockClaims`). Two parts:

  1. **Driver API.** Each kind of insert-once merge is driven directly:
     through `checkBlockClaims` then `mergeCompiledBlock` (what every driver
     does with a compiled block), through `applyAuxBlockOutcome` (the wave
     driver's merge, with two blocks of one wave claiming one name) and
     through `promoteRemaining`:
     a primary name over an aux claim, an aux claim over a compiled name, over
     an earlier aux claim and over itself within one block, an identical
     re-claim (accepted), a conflicting plan of each of the three kinds, a
     second compiled claim at another address (A7, a7s §6.2) and two
     differing Pass 3 records of one key inside one block (A7, D1).
     The messages must be Rust's, character for character.
  2. **Both compilers.** A constructed closure that bypasses the B1
     existence rule: it holds a user constant named `T.below` (a plain
     definition, not Lean's auxiliary) for a recursive inductive `T` whose
     field type depends on it, so `T.below` compiles before `T` in every
     schedule and `T`'s aux tail then regenerates and claims `T.below`. Real
     Lean input cannot contain this: Lean's own `mkBelow` would have failed
     on the name. The Rust compiler (`ix compile`'s FFI), the sequential and
     wave drivers (1, 4, 16 workers) and the `ix compile-lean` pipeline (1,
     4, 16 workers), each in both modes (`IX_PASS3=off` and Pass 3, the
     default), must all refuse exactly `T`'s block, with the same
     conflict message (same name, same two addresses); the user `T.below`
     itself compiles.

  Run with: `lake test -- --ignored compile-claim-conflict`.
-/
import Tests.Ix.Compile.Twins

open Lean

namespace Tests.Ix.Compile.ClaimConflict

namespace Fixture

/-- Stands in for a user constant named `T.below`: the constructed closure
    renames it. -/
def FakeBelow : Type := PUnit

/-- `T`'s field type. In the constructed closure its body is the user
    `T.below`, so `T`'s block depends on it. -/
def Dep : Type := FakeBelow

/-- A recursive inductive: Lean generates `T.below` for it, and so does Ix's
    aux-gen under the B1 existence rule. -/
inductive T where
  | leaf : T
  | node : Dep → T → T

end Fixture

/-! ## Part 1: the driver API -/


section DriverApi
open Ix.CompileM

private def addr (s : String) : Address := Address.blake3 s.toUTF8

private def ixName (s : String) : Ix.Name := Ix.Name.fromLeanName s.toName

/-- Rust's `name_claim_conflict` format (compile.rs:470-482), written out. -/
private def rustConflict (n : Ix.Name) (existing claimed : Address) : String :=
  s!"conflicting claims for name '{n.pretty}': already registered at \
{(toString existing).take 12}, claimed again at {(toString claimed).take 12}"

private def emptyAcc : DriverAcc := { cenv := default }

/-- A block result whose lone constant `lo` sits at `a` (no projections). -/
private def loneResult (a : Address) : BlockResult :=
  { block := default, blockBytes := ByteArray.empty, blockAddr := a }

/-- A block state whose aux tail claims `claims`, in order, the way
    `Ix.AuxGen.CompileAux` registers them. -/
private def auxCache (claims : List (Ix.Name × Address)) : BlockState := Id.run do
  let mut st : BlockState := default
  for (n, a) in claims do
    st := { st with
      auxNamed := st.auxNamed.push (n, { addr := a })
      auxNameToAddr := st.auxNameToAddr.insert n a
      auxGenExtraNames := st.auxGenExtraNames.insert n }
  return st

/-- What every driver does with a compiled block: `checkBlockClaims`, then
    `mergeCompiledBlock` if the check passes. -/
private def merge (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult) (cache : BlockState)
    (plans : Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan)
    (brecPlans belowPlans : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan) :
    Except CompileError DriverAcc := do
  checkBlockClaims acc.cenv (primaryClaims lo result) cache plans brecPlans belowPlans
  pure (mergeCompiledBlock acc lo result cache plans brecPlans belowPlans)

private def errOf : Except CompileError DriverAcc → Option String
  | .error (.invalidMutualBlock r) => some r
  | .error e => some s!"(another error) {e}"
  | .ok _ => none

private def bplan (k : Nat) : Ix.AuxGen.BRecOnCallSitePlan :=
  { nParams := k, nSourceMotives := 2, nIndices := 0, motiveKeep := #[true, false],
    sourceToCanonMotive := #[0, 0], sourceInBlock := #[true, true] }

private def cplan (k : Nat) : Ix.AuxGen.CallSitePlan :=
  { nParams := k, nSourceMotives := 2, nSourceMinors := 0, nIndices := 0,
    motiveKeep := #[true, false], minorKeep := #[], sourceToCanonMotive := #[0, 0],
    sourceToCanonMinor := #[], sourceInBlock := #[true, true], minorInBlock := #[],
    headRewrite := none }

/-- The driver-API cases: (label, expected message or `none` for accepted,
    actual). -/
def driverCases : List (String × Option String × Option String) := Id.run do
  let n := ixName "Fx.T.below"
  let lo := ixName "Fx.T"
  let x := addr "x"
  let y := addr "y"
  let withCompiled : DriverAcc :=
    { cenv := { (default : CompileEnv) with nameToAddr := ({} : Std.HashMap _ _).insert n x } }
  let withClaimed : DriverAcc :=
    { cenv := { (default : CompileEnv) with auxNameToAddr := ({} : Std.HashMap _ _).insert n x } }
  let none₀ : Std.HashMap Ix.Name Ix.AuxGen.CallSitePlan := {}
  let noneB : Std.HashMap Ix.Name Ix.AuxGen.BRecOnCallSitePlan := {}
  let mut cases : List (String × Option String × Option String) := []
  -- claim_compiled_name: a primary name aux-gen has claimed elsewhere
  cases := cases ++ [("primary name over an aux claim", some (rustConflict n x y),
    errOf (merge withClaimed n (loneResult y) default none₀ noneB noneB))]
  -- claim_aux_name over name_to_addr
  cases := cases ++ [("aux claim over a compiled name", some (rustConflict n x y),
    errOf (merge withCompiled lo (loneResult (addr "t")) (auxCache [(n, y)])
      none₀ noneB noneB))]
  -- claim_aux_name over the block's own primary name
  cases := cases ++ [("aux claim over the block's own primary name", some (rustConflict n y x),
    errOf (merge emptyAcc n (loneResult y) (auxCache [(n, x)]) none₀ noneB noneB))]
  -- claim_aux_name over an earlier aux claim
  cases := cases ++ [("aux claim over an earlier aux claim", some (rustConflict n x y),
    errOf (merge withClaimed lo (loneResult (addr "t")) (auxCache [(n, y)])
      none₀ noneB noneB))]
  -- claim_aux_name twice in one block
  cases := cases ++ [("two aux claims in one block", some (rustConflict n x y),
    errOf (merge emptyAcc lo (loneResult (addr "t")) (auxCache [(n, x), (n, y)])
      none₀ noneB noneB))]
  -- identical re-claims are no-ops
  cases := cases ++ [("identical re-claim", none,
    errOf (merge withClaimed lo (loneResult (addr "t")) (auxCache [(n, x), (n, x)])
      none₀ noneB noneB))]
  cases := cases ++ [("identical compiled name and aux claim", none,
    errOf (merge withCompiled lo (loneResult (addr "t")) (auxCache [(n, x)])
      none₀ noneB noneB))]
  -- A7 (a7s §6.2): a second compiled claim at another address
  cases := cases ++ [("second compiled claim", some (rustConflict n x y),
    errOf (merge withCompiled n (loneResult y) default none₀ noneB noneB))]
  cases := cases ++ [("identical second compiled claim", none,
    errOf (merge withCompiled n (loneResult x) default none₀ noneB noneB))]
  -- A7 (D1): two differing Pass 3 records of one key inside one block
  let p3Two : BlockState := { (default : BlockState) with
    p3Heads := #[(n, lo), (n, ixName "Fx.U")] }
  cases := cases ++ [("two Pass 3 heads in one block",
    some s!"Pass 3: conflicting image-kind head '{n.pretty}'",
    errOf (merge emptyAcc lo (loneResult (addr "t")) p3Two none₀ noneB noneB))]
  let p3Same : BlockState := { (default : BlockState) with p3Heads := #[(n, lo), (n, lo)] }
  cases := cases ++ [("identical Pass 3 heads in one block", none,
    errOf (merge emptyAcc lo (loneResult (addr "t")) p3Same none₀ noneB noneB))]
  -- plans (compile.rs:4990-5115)
  let k := ixName "Fx.A.rec"
  let withPlans : DriverAcc := { cenv := { (default : CompileEnv) with
    callSitePlans := ({} : Std.HashMap _ _).insert k (cplan 1)
    brecOnCallSitePlans := ({} : Std.HashMap _ _).insert k (bplan 1)
    belowCallSitePlans := ({} : Std.HashMap _ _).insert k (bplan 1) } }
  let one (p : Ix.AuxGen.BRecOnCallSitePlan) := ({} : Std.HashMap Ix.Name _).insert k p
  cases := cases ++ [("conflicting call-site plan",
    some s!"conflicting call-site plans for '{k.pretty}' — two blocks claim one source-indexed aux name",
    errOf (merge withPlans lo (loneResult (addr "t")) default
      (({} : Std.HashMap Ix.Name _).insert k (cplan 2)) noneB noneB))]
  cases := cases ++ [("conflicting brecOn call-site plan",
    some s!"conflicting brecOn call-site plans for '{k.pretty}' — two blocks claim one source-indexed aux name",
    errOf (merge withPlans lo (loneResult (addr "t")) default none₀ (one (bplan 2)) noneB))]
  cases := cases ++ [("conflicting below call-site plan",
    some s!"conflicting below call-site plans for '{k.pretty}' — two blocks claim one source-indexed aux name",
    errOf (merge withPlans lo (loneResult (addr "t")) default none₀ noneB (one (bplan 2))))]
  cases := cases ++ [("equal plans", none,
    errOf (merge withPlans lo (loneResult (addr "t")) default
      (({} : Std.HashMap Ix.Name _).insert k (cplan 1)) (one (bplan 1)) (one (bplan 1))))]
  -- the wave driver: two blocks of one wave, computed on one snapshot,
  -- claim `n` at different addresses; the second merge is refused and the
  -- block is reported failed (its dependents are released as failed)
  let lo₂ := ixName "Fx.U"
  let all₁ : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert lo
  let all₂ : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert lo₂
  let (acc₁, _, failed₁) := applyAuxBlockOutcome emptyAcc lo all₁
    (.compiled (loneResult (addr "t")) (auxCache [(n, x)]) none₀ noneB noneB)
  let (acc₂, names₂, failed₂) := applyAuxBlockOutcome acc₁ lo₂ all₂
    (.compiled (loneResult (addr "u")) (auxCache [(n, y)]) none₀ noneB noneB)
  let waveMsg : Option String :=
    if failed₁ || !failed₂ || !names₂.isEmpty || acc₂.cenv.auxNameToAddr.get? n != some x then
      some s!"wrong outcome: failed {failed₁}/{failed₂}, registered {names₂.size}, \
claim {acc₂.cenv.auxNameToAddr.get? n}"
    else (acc₂.cenv.ungrounded.get? lo₂).map fun m => (m.drop "invalidMutualBlock: ".length).toString
  cases := cases ++ [("wave: two blocks of one wave", some (rustConflict n x y), waveMsg)]
  -- the promote-remaining pass (env.rs:757-789): a member compiled at `x`
  -- with an aux claim at `y` is recorded, not skipped
  let both : DriverAcc := { cenv := { (default : CompileEnv) with
    nameToAddr := ({} : Std.HashMap _ _).insert n x
    auxNameToAddr := ({} : Std.HashMap _ _).insert n y } }
  let (accP, _) := promoteRemaining both (({} : Ix.Set Ix.Name).insert n)
  cases := cases ++ [("promote-remaining over a compiled member", some (rustConflict n x y),
    (accP.cenv.ungrounded.get? n).map fun m => (m.drop "invalidMutualBlock: ".length).toString)]
  return cases

/-- D11: target promotion must not change a new alias's provenance; its
own source promotion must still be retained. -/
def aliasProvenanceCheck : Except String Unit := do
  let source := ixName "Fx.A.rec_1"
  let target := ixName "Fx.B.rec"
  let canonical := addr "canonical"
  let targetOriginal := addr "target-original"
  let sourceOriginal := addr "source-original"
  let aliases := ({} : Std.HashMap Ix.Name Ix.Name).insert source target
  let blockEnv : BlockEnv :=
    { all := ({} : Ix.Set Ix.Name).insert source, current := source, mutCtx := default, univCtx := [] }
  let targetEnv (original : Option (Address × Ixon.ConstantMeta)) : CompileEnv :=
    { (default : CompileEnv) with
      nameToAddr := ({} : Std.HashMap _ _).insert target canonical
      nameToNamed := ({} : Std.HashMap _ _).insert target
        { addr := canonical, original, hints := some .abbrev } }
  let register (env : CompileEnv) :=
    (CompileM.run env blockEnv {} (Ix.AuxGen.registerAuxAliases aliases "D11 fixture"))
      |>.mapError toString
  let (_, before) ← register (targetEnv none)
  let (_, after) ← register (targetEnv (some (targetOriginal, .empty)))
  let some (n, aliasBefore) := before.auxNamed[0]? | throw "D11: missing initial alias"
  let some (_, aliasAfter) := after.auxNamed[0]? | throw "D11: missing alias after target promotion"
  if n != source || before.auxNamed.size != 1 || after.auxNamed.size != 1 then
    throw "D11: wrong alias registrations"
  if aliasBefore != aliasAfter || aliasAfter.original.isSome then
    throw "D11: alias borrowed the target's source provenance"
  if aliasAfter.addr != canonical || aliasAfter.hints != some .abbrev then
    throw "D11: canonical alias content or hints lost"
  let env := { targetEnv (some (targetOriginal, .empty)) with
    nameToNamed := (targetEnv none).nameToNamed.insert source aliasAfter
    auxNameToAddr := ({} : Std.HashMap _ _).insert source canonical }
  let promoted ← (promoteAuxDriver env source sourceOriginal .empty).mapError toString
  let some own := promoted.nameToNamed.get? source | throw "D11: own promotion missing"
  if own.original != some (sourceOriginal, .empty) || own.addr != canonical then
    throw "D11: own source provenance was not preserved"
  let (_, repeated) ← register promoted
  if !repeated.auxNamed.isEmpty then
    throw "D11: consistent re-registration overwrote the source's own original"

end DriverApi

/-! ## Part 2: both compilers on a constructed closure -/

/-- The aux-gen seed names (`Ix.CompileM.auxGenSeedNames`), as Lean names. -/
def auxSeeds : List Name :=
  [``PUnit, ``PProd, ``Eq, ``Eq.refl, ``Eq.symm, ``Eq.ndrec, ``rfl, ``HEq, ``HEq.refl,
    ``eq_of_heq, ``True]

def tName : Name := ``Fixture.T
def belowName : Name := tName ++ `below

/-- The closure of `T` and `Dep`, with `FakeBelow` renamed to `T.below` and
    `Dep`'s body pointing at it. Lean's own auxiliaries of `T` are not in it:
    nothing in the closure references them. -/
def conflictClosure (env : Environment) : Except String (List (Name × ConstantInfo)) := do
  let some (.defnInfo fv) := env.find? ``Fixture.FakeBelow | throw "FakeBelow missing"
  let some (.defnInfo dv) := env.find? ``Fixture.Dep | throw "Dep missing"
  if (dv.value.getUsedConstants.contains ``Fixture.FakeBelow) == false then
    throw "Dep does not mention FakeBelow"
  let base := Tests.Ix.Compile.Twins.closeWithRecursors env
    (Ix.EnvScope.collectDeps env ([``Fixture.Dep, tName, tName ++ `rec] ++ auxSeeds))
  let userBelow : ConstantInfo := .defnInfo { fv with name := belowName, all := [belowName] }
  let dep' : ConstantInfo := .defnInfo { dv with value := .const belowName [] }
  let rest := base.filterMap fun (n, ci) =>
    if n == ``Fixture.FakeBelow then none
    else if n == ``Fixture.Dep then some (n, dep')
    else some (n, ci)
  return (belowName, userBelow) :: rest

/-- The message without the error-kind prefix: Rust prints
    `invalid mutual block: …`, Lean `invalidMutualBlock: …` (the two
    compilers' `CompileError` spellings differ for every error). -/
def core (msg : String) : String :=
  match msg.splitOn ": " with
  | _ :: rest@(_ :: _) => ": ".intercalate rest
  | _ => msg

/-- A missing-dependency cascade, in either compiler's spelling. -/
def isCascadeRaw (msg : String) : Bool :=
  msg.startsWith "missingConstant" || msg.startsWith "missing constant"

/-- Sorted (name, message) pairs, messages without the error-kind prefix;
    cascades are marked `missing …`. -/
def sorted (xs : List (String × String)) : List (String × String) :=
  (xs.map fun (n, m) => (n, if isCascadeRaw m then s!"missing {core m}" else core m)).toArray.qsort
    (fun a b => a.1 < b.1) |>.toList

def isCascade (msg : String) : Bool := msg.startsWith "missing "

def run : IO UInt32 := do
  let mut failures := 0
  match aliasProvenanceCheck with
  | .ok () => IO.println "[claim-conflict] alias provenance: target promotion independent; own original preserved"
  | .error e =>
    failures := failures + 1
    IO.println s!"[claim-conflict] alias provenance: FAIL: {e}"
  -- Part 1
  for (label, expected, actual) in driverCases do
    if expected == actual then
      IO.println s!"[claim-conflict] driver: {label}: {actual.getD "accepted"}"
    else
      failures := failures + 1
      IO.println s!"[claim-conflict] driver: {label}: FAIL: expected {expected.getD "accepted"}, \
got {actual.getD "accepted"}"
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
  let rust := sorted status.ungrounded.toList
  for (n, m) in rust do
    IO.println s!"[claim-conflict] rust refuses {n}: {m}"
  let belowPretty := (Ix.Name.fromLeanName belowName).pretty
  let tPretty := (Ix.Name.fromLeanName tName).pretty
  let isConflict (m : String) :=
    m == s!"auxiliary claim for source name '{belowPretty}' has no forward provenance to the claiming block"
  if !(rust.any fun (n, m) => n == tPretty && isConflict m) then
    failures := failures + 1
    IO.println s!"[claim-conflict] FAIL: Rust does not refuse {tPretty} with the conflicting claim on {belowPretty}"
  if rust.any (·.1 == belowPretty) then
    failures := failures + 1
    IO.println s!"[claim-conflict] FAIL: Rust refuses the user {belowPretty} itself"
  -- Lean: every schedule
  let mut runs : Array (String × List (String × String)) := #[]
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  for (ln, _) in closure do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    nameByHash := nameByHash.insert ixn.getHash ixn
  -- Both modes, explicitly: the legacy surgery (`IX_PASS3=off`, the mode the
  -- Rust compiler implements until M6R) and Pass 3 (the default). `T`'s block
  -- is not changed, so both must refuse it exactly as Rust does.
  for pass3 in [false, true] do
    let mode := if pass3 then "pass3" else "off"
    match Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed (nameByHash := nameByHash)
        (pass3 := pass3) with
    | .error e => throw (IO.userError s!"[claim-conflict] sequential driver ({mode}): {e}")
    | .ok (_, _, cenv) =>
      runs := runs.push (s!"sequential ({mode})", cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
    for k in [1, 4, 16] do
      match ← Ix.CompileM.compileEnvParallelAux phases.rawEnv phases.condensed (numWorkers := k)
          (nameByHash := nameByHash) (pass3? := some pass3) with
      | .error e => throw (IO.userError s!"[claim-conflict] wave driver, {k} workers ({mode}): {e}")
      | .ok (_, _, cenv) =>
        runs := runs.push (s!"wave --jobs {k} ({mode})", cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
    for k in [1, 4, 16] do
      let out ← Tests.Ix.Compile.Twins.leanCompile env closure k (pass3? := some pass3)
      runs := runs.push (s!"compile-lean --workers {k} ({mode})",
        out.cenv.ungrounded.toList.map fun (n, m) => (n.pretty, m))
  -- Root refusals (every failure that is not a missing-dependency cascade)
  -- must be Rust's in every schedule, name for name and message for message.
  -- The cascades differ by exactly `T.rec`: Rust registers the primary
  -- names of `T`'s block (`claim_compiled_name`, compile.rs:4740-4800)
  -- before its aux tail raises the conflict (compile.rs:4855), so `T.rec`,
  -- a block of its own, compiles in Rust against a block that failed. The
  -- Lean drivers merge nothing of a refused block (`checkBlockClaims` runs
  -- first), so `T.rec` cascades. Pinned so that a change on either side
  -- shows up here.
  let leanOnlyCascades : List String := [(Ix.Name.fromLeanName (tName ++ `rec)).pretty]
  let rustRoots := rust.filter (!isCascade ·.2)
  if rust.any (isCascade ·.2) then
    failures := failures + 1
    IO.println s!"[claim-conflict] FAIL: Rust now reports cascades: {rust.filter (isCascade ·.2)}"
  let mut reference : Option (List (String × String)) := none
  for (label, refusals) in runs do
    let lean := sorted refusals
    let roots := lean.filter (!isCascade ·.2)
    let cascades := (lean.filter (isCascade ·.2)).map (·.1)
    if roots == rustRoots && cascades == leanOnlyCascades then
      IO.println s!"[claim-conflict] {label}: {roots.length} refusals identical to Rust's; \
cascade {cascades} (Rust compiles it)"
    else
      failures := failures + 1
      IO.println s!"[claim-conflict] {label}: FAIL: refusals differ from Rust"
      for (n, m) in lean do
        IO.println s!"[claim-conflict]   lean {n}: {m}"
    match reference with
    | none => reference := some lean
    | some r =>
      if r != lean then
        failures := failures + 1
        IO.println s!"[claim-conflict] {label}: FAIL: refusals differ from the sequential driver's"
  IO.println s!"[claim-conflict] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ClaimConflict
