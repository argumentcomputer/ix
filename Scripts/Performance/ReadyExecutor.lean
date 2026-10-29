
import Ix.Compile.ReadyQueue
import Ix.Cert.Schedule
import Init.System.Promise

/-! Native controls for the ready executor. Constructed source values exercise
refusal, metadata and resource bounds; they are not claims of admitted Lean
declarations. Explicit pending-worker drain controls are added separately.
-/

namespace ReadyExecutor

open _root_.Ix.CompileM _root_.Ix.Compile.WorkerReplay
open _root_.Ix.Compile.ReadyQueue

private def need (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def awaitIO (task : Task (Except IO.Error α)) : IO α := do
  match ← IO.wait task with
  | .ok value => return value
  | .error error => throw error

structure Fixture where
  source : _root_.Ix.Environment
  blocks : _root_.Ix.CondensedBlocks
  names : Array _root_.Ix.Name

private def fixture (count layerWidth : Nat) (failures := false) (omitDeps := false) : Fixture := Id.run do
  let base := _root_.Ix.Name.fromLeanName `SchedulerControl
  let mut source : _root_.Ix.Environment := { consts := {} }
  let mut blocks : _root_.Ix.CondensedBlocks := { lowLinks := {}, blocks := {}, blockRefs := {} }
  let mut names := #[]
  for index in [:count] do
    let name := _root_.Ix.Name.mkNat base index
    let parent := if index < layerWidth then none else some (_root_.Ix.Name.mkNat base (index - layerWidth))
    let normal := match parent with
      | none => _root_.Ix.Expr.mkLit (.strVal "window literal")
      | some prior => _root_.Ix.Expr.mkConst prior #[]
    let body := if failures && index % 11 == 3 then
      _root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkLit (.strVal "discarded literal")) (_root_.Ix.Expr.mkBVar UInt64.size)
      else normal
    let declaration : _root_.Ix.ConstantInfo := .defnInfo {
      cnst := { name, levelParams := #[], type := _root_.Ix.Expr.mkSort (_root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero) }
      value := body, hints := .opaque, safety := .safe, all := #[name] }
    source := { source with consts := source.consts.insert name declaration }
    let members : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert name
    let dependencies : _root_.Ix.Set _root_.Ix.Name := if omitDeps then {} else
      match parent with | none => {} | some prior => ({} : _root_.Ix.Set _root_.Ix.Name).insert prior
    blocks := { lowLinks := blocks.lowLinks.insert name name
                blocks := blocks.blocks.insert name members
                blockRefs := blocks.blockRefs.insert name dependencies }
    names := names.push name
  return { source, blocks, names }

private def mutualFixture : Fixture := Id.run do
  let left := _root_.Ix.Name.fromLeanName `SchedulerMutual.left
  let right := _root_.Ix.Name.fromLeanName `SchedulerMutual.right
  let consumer := _root_.Ix.Name.fromLeanName `SchedulerMutual.consumer
  let group := #[left, right]
  let declaration (name target : _root_.Ix.Name) (all : Array _root_.Ix.Name) : _root_.Ix.ConstantInfo := .defnInfo {
    cnst := { name, levelParams := #[], type := _root_.Ix.Expr.mkSort (_root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero) }
    value := _root_.Ix.Expr.mkConst target #[], hints := .opaque, safety := .safe, all }
  let mut source : _root_.Ix.Environment := { consts := {} }
  source := { source with consts := source.consts.insert left (declaration left right group) }
  source := { source with consts := source.consts.insert right (declaration right left group) }
  source := { source with consts := source.consts.insert consumer (declaration consumer left #[consumer]) }
  let members : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert left |>.insert right
  let single : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert consumer
  let dependencies : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert left
  let blocks : _root_.Ix.CondensedBlocks := {
    lowLinks := ({} : _root_.Ix.Map _root_.Ix.Name _root_.Ix.Name).insert left left |>.insert right left |>.insert consumer consumer
    blocks := ({} : _root_.Ix.Map _root_.Ix.Name (_root_.Ix.Set _root_.Ix.Name)).insert left members |>.insert consumer single
    blockRefs := ({} : _root_.Ix.Map _root_.Ix.Name (_root_.Ix.Set _root_.Ix.Name)).insert left {} |>.insert consumer dependencies }
  return { source, blocks, names := #[left, right, consumer] }

private def sameState (left right : FoldState) : Bool :=
  left.remaining == right.remaining && left.waves == right.waves &&
  left.settled.toArray == right.settled.toArray && left.unmet.toArray == right.unmet.toArray &&
  left.candidates == right.candidates &&
  left.acc.cenv.nameToAddr.toArray == right.acc.cenv.nameToAddr.toArray &&
  left.acc.cenv.nameToNamed.toArray == right.acc.cenv.nameToNamed.toArray &&
  left.acc.cenv.constants.toArray == right.acc.cenv.constants.toArray &&
  left.acc.cenv.blobs.toArray == right.acc.cenv.blobs.toArray &&
  left.acc.cenv.ungrounded.toArray == right.acc.cenv.ungrounded.toArray &&
  left.acc.cenv.blocks.toArray == right.acc.cenv.blocks.toArray &&
  left.acc.cenv.totalBytes == right.acc.cenv.totalBytes &&
  left.acc.blockNames.toArray == right.acc.blockNames.toArray &&
  (left.acc.defHints.toArray.map fun (name, hints) => (name, reprStr hints)) ==
    (right.acc.defHints.toArray.map fun (name, hints) => (name, reprStr hints))

private def sameResult : Except String FoldState → Except String FoldState → Bool
  | .error left, .error right => left == right
  | .ok left, .ok right => sameState left right
  | _, _ => false

private def encoded (state : FoldState) : Except String ByteArray := do
  let (artifact, _, _) ← finalizeEnv state.acc
  Ixon.serEnv artifact

private def sameBytes : Except String ByteArray → Except String ByteArray → Bool
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

private def compareFold (label : String) (data : Fixture) (env : CompileEnv)
    (requireBytes := true) : IO Unit := do
  let schedule := FoldSchedule.of data.blocks
  let initial := FoldState.init env data.blocks schedule
  let fuel := data.blocks.blocks.size + 1
  let expected ← IO.lazyPure fun _ => foldWaves data.blocks schedule 256 false fuel initial
  let configurations : List Config := [
    { workers := 0, lookahead := 0, pendingEdges := 0, payloadBytes := 0 },
    { workers := 1, lookahead := 1 },
    { workers := 4, lookahead := 7, pendingEdges := 3, payloadBytes := 256 },
    { workers := 8, lookahead := 128 }]
  for config in configurations do
    let (actual, metrics) ← _root_.Ix.Compile.ReadyQueue.run config data.blocks schedule
      256 false fuel initial
    need s!"{label}: complete fold result/refusal differs" (sameResult expected actual.val)
    need s!"{label}: workers were not completely consumed"
      (metrics.started == metrics.completed + metrics.drained)
    need s!"{label}: speculative block-worker bound exceeded"
      (metrics.maxActive ≤ config.workers - 1)
    need s!"{label}: admission bound exceeded"
      (metrics.maxAdmitted ≤ max 1 config.lookahead)
    need s!"{label}: pending-edge bound exceeded"
      (metrics.maxPendingEdges ≤ config.pendingEdges)
    match expected, actual.val with
    | .ok left, .ok right =>
      let expectedBytes := encoded left
      if requireBytes then need s!"{label}: reference serialization failed" expectedBytes.isOk
      need s!"{label}: serialized full/partial result differs"
        (sameBytes expectedBytes (encoded right))
    | _, _ => pure ()
    IO.println s!"PASS {label}: {repr metrics}"

private def parityChecks : IO Unit := do
  let data := fixture 40 8 true
  let env := { CompileEnv.new data.source with sharingLimits := compilerSharingLimits }
  compareFold "success, worker refusal and missing-parent cascade" data env
  let collision := { env with
    blobs := env.blobs.insert
      (Address.admissionHash "discarded literal".toUTF8) "different payload".toUTF8 }
  let some bad := data.names[3]? | throw (IO.userError "missing refusal fixture")
  let badMembers : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert bad
  need "reference refusal did not reach the index limit" (match runBlock env badMembers bad with
    | .error (.resourceLimit _) => true | _ => false)
  need "ambient collision did not change the first refusal" (match runBlock collision badMembers bad with
    | .error (.invalidMutualBlock "anonymous publication: conflicting blob payload") => true
    | _ => false)
  compareFold "ambient collision preserves the first reference error" data collision
  let omitted := fixture 24 8 false true
  compareFold "omitted dependencies keep the original frozen snapshot" omitted
    { CompileEnv.new omitted.source with sharingLimits := compilerSharingLimits }
  let clean := fixture 24 8
  let cleanEnv := { CompileEnv.new clean.source with sharingLimits := compilerSharingLimits }
  let some root := clean.names[0]? | throw (IO.userError "missing root")
  let members : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert root
  let .ok (result, cache) := runBlock cleanEnv members root
    | throw (IO.userError "clean root did not compile")
  let blocked := { cleanEnv with
    constants := cleanEnv.constants.insert result.blockAddr "conflicting record".toUTF8 }
  need "parent-publication control did not refuse"
    (applyAuxBlockOutcome { cenv := blocked } root members (.compiled result cache)).2.2
  compareFold "computed parent rejected during publication" clean blocked false
  compareFold "rejected parent keeps the earlier primary address" clean
    { cleanEnv with
      nameToAddr := cleanEnv.nameToAddr.insert root
        (Address.admissionHash "older claim".toUTF8) }
  let family := mutualFixture
  compareFold "mutual member slots, projections and metadata" family
    { CompileEnv.new family.source with sharingLimits := compilerSharingLimits }
  let malformed := { clean with blocks := { clean.blocks with
    blockRefs := clean.blocks.blockRefs.erase root } }
  compareFold "missing dependency row keeps reference behavior" malformed cleanEnv false

private def reuseControl : IO Unit := do
  let data := fixture 32 8
  let env := { CompileEnv.new data.source with sharingLimits := compilerSharingLimits }
  let schedule := FoldSchedule.of data.blocks
  let initial := FoldState.init env data.blocks schedule
  let (actual, metrics) ← _root_.Ix.Compile.ReadyQueue.run
    { workers := 8, lookahead := 128 } data.blocks schedule 256 false
    (data.blocks.blocks.size + 1) initial
  need "clean dependency graph did not complete" actual.val.isOk
  need "clean dependency graph silently recomputed workers"
    (metrics.reused == data.blocks.blocks.size && metrics.fallbackRequests == 0 &&
      metrics.sourceFallbacks == 0 && metrics.failedFallbacks == 0 &&
      metrics.addressFallbacks == 0 && metrics.blobFallbacks == 0)
  need "clean dependency graph did not consume all tasks"
    (metrics.started == metrics.completed + metrics.drained)
  IO.println s!"PASS successful reuse without reference recomputation: {repr metrics}"

private def exactSourceControl : IO Unit := do
  let name := _root_.Ix.Name.fromLeanName `ReadyExactSource
  let other := match name with
    | .str parent text hash => _root_.Ix.Name.str parent (text ++ "Different") hash
    | _ => name
  need "stored-hash collision fixture is not distinct"
    (name == other && decide (name ≠ other))
  let declaration (key : _root_.Ix.Name) (text : String) : _root_.Ix.ConstantInfo := .defnInfo {
    cnst := {
      name := key
      levelParams := #[]
      type := _root_.Ix.Expr.mkSort (_root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero) }
    value := _root_.Ix.Expr.mkLit (.strVal text), hints := .opaque, safety := .safe, all := #[key] }
  let lookup := fun query =>
    if query = name then some (declaration name "actual source")
    else if query = other then some (declaration other "different source") else none
  let source : _root_.Ix.Environment := { consts := {}, fallback? := some lookup }
  let env := { CompileEnv.new source with sharingLimits := compilerSharingLimits }
  let input := FixedInput.ofEnv env
  let members : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert name
  let otherMembers : _root_.Ix.Set _root_.Ix.Name := ({} : _root_.Ix.Set _root_.Ix.Name).insert other
  let candidate := speculate input other otherMembers {}
  let some (different, _) := candidate.compiled
    | throw (IO.userError "different-source candidate did not compile")
  let .compiled expected expectedState := auxBlockOutcome env name members
    | throw (IO.userError "actual source did not compile")
  need "different-source candidate has the same bytes" (different.blockBytes != expected.blockBytes)
  let .compiled actual actualState := checkedOutcome input env name members candidate
    | throw (IO.userError "checked source replay failed")
  need "stored-hash alias authorized another source"
    (actual.blockBytes == expected.blockBytes &&
      actualState.blockBlobs.toArray == expectedState.blockBlobs.toArray)
  IO.println "PASS exact source identity"

def run : IO UInt32 := do
  exactSourceControl
  reuseControl
  parityChecks
  IO.println "Ready executor fixture controls PASS"
  return 0

end ReadyExecutor

def main (_args : List String) : IO UInt32 := ReadyExecutor.run
