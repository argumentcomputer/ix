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
     re-claim (accepted), a second compiled claim at another address (A7, a7s §6.2) and two
     differing Pass 3 records of one key inside one block (A7, D1).
     The messages must be Rust's, character for character.
  2. **Both compilers.** A closure holds a user definition named `T.below`
     before the recursive inductive `T`, whose field type depends on it.
     `Lean.addDecl` permits this source shape (the kernel-checked neighbor is
     in `Fixtures.AuxiliaryIdentity`). Derived generated helpers use reserved
     identities, so this must compile while preserving the existing source
     binding. Rust, both Lean drivers and the full Lean pipeline at the
     original worker counts must agree byte for byte and recover the supplied
     source. The direct duplicate-claim and rollback checks above still refuse
     genuine conflicting writes.

  Run with: `lake test -- --ignored compile-claim-conflict`.
-/
import Tests.Ix.Compile.Pass3

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
private def merge (acc : DriverAcc) (lo : Ix.Name) (result : BlockResult) (cache : BlockState) :
    Except CompileError DriverAcc := do
  checkBlockClaims acc.cenv (primaryClaims lo result) cache
  pure (mergeCompiledBlock acc lo result cache)

private def errOf : Except CompileError DriverAcc → Option String
  | .error (.invalidMutualBlock r) => some r
  | .error e => some s!"(another error) {e}"
  | .ok _ => none

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
  let mut cases : List (String × Option String × Option String) := []
  -- claim_compiled_name: a primary name aux-gen has claimed elsewhere
  cases := cases ++ [("primary name over an aux claim", some (rustConflict n x y),
    errOf (merge withClaimed n (loneResult y) default))]
  -- claim_aux_name over name_to_addr
  cases := cases ++ [("aux claim over a compiled name", some (rustConflict n x y),
    errOf (merge withCompiled lo (loneResult (addr "t")) (auxCache [(n, y)])))]
  -- claim_aux_name over the block's own primary name
  cases := cases ++ [("aux claim over the block's own primary name", some (rustConflict n y x),
    errOf (merge emptyAcc n (loneResult y) (auxCache [(n, x)])))]
  -- claim_aux_name over an earlier aux claim
  cases := cases ++ [("aux claim over an earlier aux claim", some (rustConflict n x y),
    errOf (merge withClaimed lo (loneResult (addr "t")) (auxCache [(n, y)])))]
  -- claim_aux_name twice in one block
  cases := cases ++ [("two aux claims in one block", some (rustConflict n x y),
    errOf (merge emptyAcc lo (loneResult (addr "t")) (auxCache [(n, x), (n, y)])))]
  -- identical re-claims are no-ops
  cases := cases ++ [("identical re-claim", none,
    errOf (merge withClaimed lo (loneResult (addr "t")) (auxCache [(n, x), (n, x)])))]
  cases := cases ++ [("identical compiled name and aux claim", none,
    errOf (merge withCompiled lo (loneResult (addr "t")) (auxCache [(n, x)])))]
  -- A7 (a7s §6.2): a second compiled claim at another address
  cases := cases ++ [("second compiled claim", some (rustConflict n x y),
    errOf (merge withCompiled n (loneResult y) default))]
  cases := cases ++ [("identical second compiled claim", none,
    errOf (merge withCompiled n (loneResult x) default))]
  -- A7 (D1): two differing Pass 3 records of one key inside one block
  let p3Two : BlockState := { (default : BlockState) with
    p3Heads := #[(n, lo), (n, ixName "Fx.U")] }
  cases := cases ++ [("two Pass 3 heads in one block",
    some s!"Pass 3: conflicting image-kind head '{n.pretty}'",
    errOf (merge emptyAcc lo (loneResult (addr "t")) p3Two))]
  let p3Same : BlockState := { (default : BlockState) with p3Heads := #[(n, lo), (n, lo)] }
  cases := cases ++ [("identical Pass 3 heads in one block", none,
    errOf (merge emptyAcc lo (loneResult (addr "t")) p3Same))]
  -- the wave driver: two blocks of one wave, computed on one snapshot,
  -- claim `n` at different addresses; the second merge is refused and the
  -- block is reported failed (its dependents are released as failed)
  let lo₂ := ixName "Fx.U"
  let all₁ : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert lo
  let all₂ : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert lo₂
  let (acc₁, _, failed₁) := applyAuxBlockOutcome emptyAcc lo all₁
    (.compiled (loneResult (addr "t")) (auxCache [(n, x)]))
  let (acc₂, names₂, failed₂) := applyAuxBlockOutcome acc₁ lo₂ all₂
    (.compiled (loneResult (addr "u")) (auxCache [(n, y)]))
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

/-- Original-form publication is conditional on the entire promotion succeeding,
including writes for a different member visited by the source-family compiler. -/
def promotionCases : List (String × Bool) := Id.run do
  let a := ixName "Fx.Promote.a"
  let b := ixName "Fx.Promote.b"
  let other := ixName "Fx.Promote.other"
  let canonical := addr "promotion-canonical"
  let original := addr "promotion-original"
  let different := addr "promotion-conflict"
  let all : Ix.Set Ix.Name := (({} : Ix.Set Ix.Name).insert a).insert b
  let acc : DriverAcc :=
    { cenv := { (default : CompileEnv) with
        auxNameToAddr := ({} : Std.HashMap _ _).insert a canonical |>.insert b canonical
        nameToNamed := ({} : Std.HashMap _ _).insert a { addr := canonical }
          |>.insert b { addr := canonical } |>.insert other { addr := canonical }
        nameToAddr := ({} : Std.HashMap _ _).insert other canonical
        auxGenExtraNames := all
        constants := ({} : Std.HashMap _ _).insert canonical ByteArray.empty }
      defHints := ({} : Std.HashMap _ _).insert a .abbrev |>.insert other .opaque
      pending := #[a, b, other] }
  let withdrawn (out : DriverAcc) : Bool :=
    all.toList.all (fun n => (resolveAddrPure out.cenv n).isNone &&
      !out.cenv.nameToNamed.contains n && !out.cenv.auxGenExtraNames.contains n &&
      out.cenv.ungrounded.contains n && !out.defHints.contains n && !out.pending.contains n)
  let untouched (out : DriverAcc) : Bool :=
    out.cenv.nameToNamed.get? other == acc.cenv.nameToNamed.get? other &&
    out.cenv.nameToAddr.get? other == some canonical &&
    out.defHints.get? other == some .opaque && out.cenv.constants.contains canonical
  let (failed, names, bad) := applyAuxBlockOutcome acc a all
    (.promoted none #[] none none (some "original compile refused"))
  let mut cases := [("no-aux refusal withdraws all provisional names",
    bad && names.isEmpty && withdrawn failed && untouched failed)]
  let (incomplete, names, bad) := applyAuxBlockOutcome acc a all
    (.promoted none #[] (some "incomplete auxiliary family") none none)
  cases := cases ++ [("incomplete family has no public residue",
    bad && names.isEmpty && withdrawn incomplete && untouched incomplete)]
  let malformed : Ixon.ConstantMeta := { Ixon.ConstantMeta.empty with
    info := .axio different #[] {} 0 }
  let lateBad : BlockResult := { loneResult original with projections :=
    #[(other, default, .empty), (a, default, malformed)] }
  let (lateFailure, names, bad) := finishAuxPromotion acc a all (some (lateBad, default))
  cases := cases ++ [("late self-name failure discards earlier outside-SCC original",
    bad && names.isEmpty && withdrawn lateFailure && untouched lateFailure)]
  let conflict := { acc with cenv := { acc.cenv with
    nameToAddr := acc.cenv.nameToAddr.insert b different } }
  let outside : BlockResult := { loneResult original with projections :=
    #[(other, default, .empty)] }
  let (claimFailure, names, bad) := finishAuxPromotion conflict a all
    (some (outside, default))
  cases := cases ++ [("remaining-claim failure discards staged originals",
    bad && names.isEmpty && withdrawn claimFailure && untouched claimFailure)]
  let (ok, _, bad) := finishAuxPromotion acc a all (some (loneResult original, default))
  cases := cases ++ [("valid neighbor promotes canonical addresses and own original",
    !bad && all.toList.all (fun n => ok.cenv.nameToAddr.get? n == some canonical) &&
    ((ok.cenv.nameToNamed.get? a).bind (·.original)) == some (original, .empty) &&
    ok.cenv.ungrounded.isEmpty && untouched ok)]
  let sourceOwned := fun n => all.contains n
  cases := cases ++ [("source dependency waits despite provisional resolution",
    !auxDependencyReady sourceOwned acc.cenv {} a &&
    auxDependencyReady sourceOwned acc.cenv all a &&
    auxDependencyReady sourceOwned acc.cenv {} other &&
    !auxDependencyReady sourceOwned acc.cenv {} (ixName "Fx.Promote.absent"))]
  return cases

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
  for (label, passed) in promotionCases do
    if passed then
      IO.println s!"[claim-conflict] promotion: {label}: PASS"
    else
      failures := failures + 1
      IO.println s!"[claim-conflict] promotion: {label}: FAIL"
  -- Part 2
  let env ← get_env!
  let closure ← IO.ofExcept (conflictClosure env)
  IO.println s!"[claim-conflict] constructed closure: {closure.length} constants"
  -- A generated helper must not claim the already-settled source spelling.
  let dir : System.FilePath := "plans/tasks/lean-to-ixon-correctness/claim-conflict-gate"
  IO.FS.createDirAll dir
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants env closure)
  let status ← Ix.CompileM.rsCompileEnvBytesFFI prepared (dir / "rs.ixe").toString false
  let rust := sorted status.ungrounded.toList
  for (n, m) in rust do
    IO.println s!"[claim-conflict] rust refuses {n}: {m}"
  unless rust.isEmpty do throw (IO.userError "Rust rejected the source-owned below fixture")
  let rustBytes ← IO.FS.readBinFile (dir / "rs.ixe")
  let checkOutput (label : String) (output : Ixon.Env) (cenv : Ix.CompileM.CompileEnv) : IO Unit := do
    unless cenv.ungrounded.isEmpty do throw (IO.userError s!"{label}: source-owned below fixture refused")
    for (name, _) in closure do
      unless output.named.contains (Ix.Name.fromLeanName name) do
        throw (IO.userError s!"{label}: source declaration missing: {name}")
    let sourceName := Ix.Name.fromLeanName belowName
    let generatedName := Ix.Name.mkStr (Ix.Name.mkStr (Ix.Name.fromLeanName tName) "_ix") "below"
    let some source := output.getNamed? sourceName | throw (IO.userError "source below missing")
    let some generated := output.getNamed? generatedName | throw (IO.userError "generated below missing")
    unless source.addr != generated.addr do
      throw (IO.userError s!"{label}: generated helper replaced the source definition")
    unless (← IO.ofExcept (Ixon.serEnv output)) == rustBytes do
      throw (IO.userError s!"{label}: serialized output differs from Rust")
    let original := (Ix.CanonM.canonChunk prepared.toArray).foldl
      (fun m (name, ci) => m.insert name ci) ({} : Std.HashMap Ix.Name Ix.ConstantInfo)
    let (recovered, errors, _) ← Ix.DecompileM.decompileEnvFullParallel output (some original)
    unless errors.isEmpty && recovered.size == original.size &&
        original.toArray.all (fun (name, ci) => recovered.get? name == some ci) do
      throw (IO.userError s!"{label}: source round-trip differs")
    IO.println s!"[claim-conflict] {label}: all source names preserved; separate generated below; \
exact source round-trip; BYTE-IDENTICAL to Rust"
  -- Lean: every schedule
  let phases ← Ix.CompileM.rsCompilePhasesOf closure
  let mut nameByHash : Std.HashMap Address Ix.Name := {}
  for (ln, _) in closure do
    let (ixn, _) := StateT.run (Ix.CanonM.canonName ln) {}
    nameByHash := nameByHash.insert ixn.getHash ixn
  -- Keep every original schedule, now requiring successful source preservation.
  do
    let mode := "pass3"
    match Ix.CompileM.compileEnvAux phases.rawEnv phases.condensed (nameByHash := nameByHash) with
    | .error e => throw (IO.userError s!"[claim-conflict] sequential driver ({mode}): {e}")
    | .ok (output, _, cenv) => checkOutput s!"sequential ({mode})" output cenv
    for k in [1, 4, 16] do
      match ← Ix.CompileM.compileEnvParallelAux phases.rawEnv phases.condensed (numWorkers := k)
          (nameByHash := nameByHash) with
      | .error e => throw (IO.userError s!"[claim-conflict] wave driver, {k} workers ({mode}): {e}")
      | .ok (output, _, cenv) => checkOutput s!"wave --jobs {k} ({mode})" output cenv
    for k in [1, 4, 16] do
      let out ← Tests.Ix.Compile.Twins.leanCompile env closure k
      checkOutput s!"compile-lean --workers {k} ({mode})" out.env out.cenv
  let names := closure.toArray.map (fun (name, _) => name.toString)
  let checks := dir / "kernels"
  IO.FS.createDirAll checks
  let run ← Tests.Ix.Compile.Pass3.kernelRun checks (dir / "rs.ixe") names
  unless run.failed.isEmpty && run.checked.all (fun (_, count) => count == run.targets.size) do
    throw (IO.userError s!"source-owned below kernel checks failed: {run.failed}; {run.checked}")
  IO.println s!"[claim-conflict] {if failures == 0 then "PASS" else s!"FAIL ({failures})"}"
  return if failures == 0 then 0 else 1

end Tests.Ix.Compile.ClaimConflict
