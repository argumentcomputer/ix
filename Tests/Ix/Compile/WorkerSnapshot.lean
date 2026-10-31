module

public import Ix.CompileDriver
public import LSpec

/-! Constructed caller states test the worker's read boundary. Some source
expressions and unused output fields are deliberately malformed; these are
refusal and field-independence controls, not well-typed source or admitted
artifact fixtures. -/

namespace Tests.Ix.Compile.WorkerSnapshot

open _root_.Ix (Name Expr Level)
open _root_.Ix.CompileM

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private def sameOutcome : AuxBlockOutcome → AuxBlockOutcome → Bool
  | .failed left, .failed right => left == right
  | .compiled left ls, .compiled right rs =>
    left.block == right.block && left.blockBytes == right.blockBytes && left.blockAddr == right.blockAddr &&
    left.blockMeta == right.blockMeta && left.projections == right.projections && left.classNames == right.classNames &&
    ls.blockBlobs.toArray == rs.blockBlobs.toArray && ls.blockNames.toArray == rs.blockNames.toArray &&
    ls.blockNameToAddr.toArray == rs.blockNameToAddr.toArray && ls.mutsNamed == rs.mutsNamed &&
    (ls.defHints.toArray.map fun (n, h) => (n, reprStr h)) ==
      (rs.defHints.toArray.map fun (n, h) => (n, reprStr h))
  | _, _ => false

private def sameOutcomes (left right : Array (Name × _root_.Ix.Set Name × AuxBlockOutcome)) : Bool :=
  left.size == right.size && (left.zip right).all fun ((ln, la, lo), (rn, ra, ro)) =>
    ln == rn && la.toArray == ra.toArray && sameOutcome lo ro

private def fixture (count : Nat) : CompileEnv × Array (Name × Name × _root_.Ix.Set Name) := Id.run do
  let base := Name.fromLeanName `WorkerSnapshotFixture
  let dependency := Name.fromLeanName `WorkerSnapshotDependency
  let address := Address.admissionHash "resolved dependency".toUTF8
  let mut source : _root_.Ix.Environment := { consts := {} }
  let mut ready := #[]
  for i in [:count] do
    let name := Name.mkNat base i
    let body := match i % 5 with
      | 0 => Expr.mkLit (.strVal "worker literal")
      | 1 => Expr.mkConst dependency #[]
      | 2 => Expr.mkBVar UInt64.size
      | 3 => Expr.mkMVar name
      | _ => Expr.mkSort Level.mkZero
    let value : _root_.Ix.ConstantInfo := .defnInfo {
      cnst := { name, levelParams := #[], type := Expr.mkSort (Level.mkSucc Level.mkZero) }
      value := body, hints := .opaque, safety := .safe, all := #[name] }
    source := { source with consts := source.consts.insert name value }
    ready := ready.push (name, name, ({} : _root_.Ix.Set Name).insert name)
  let unused := Name.fromLeanName `UnusedDriverOutput
  let snapshot : CompileEnv := {
    CompileEnv.new source with
    nameToAddr := ({} : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address).insert dependency address
    nameToNamed := ({} : Std.HashMap Name Ixon.Named).insert unused { addr := address }
    constants := ({} : Std.HashMap Address ByteArray).insert address (ByteArray.mk #[255])
    totalBytes := 123456
    ungrounded := ({} : Std.HashMap Name String).insert unused "earlier refusal"
    blocks := ({} : Std.HashMap Name (Array (Array Name))).insert unused #[#[unused]] }
  return (snapshot, ready)

private def compareTasks (label : String) (snapshot : CompileEnv)
    (ready : Array (Name × Name × _root_.Ix.Set Name)) : Except String Unit := do
  -- auxBlockOutcome retains the original full-environment implementation;
  -- the production csimp changes only waveTasks.
  let expected := ready.map fun (key, _, all) => (key, all, auxBlockOutcome snapshot key all)
  for width in [0, 1, 8, 256, 1024] do
    let explicit := ((waveTasksProjected width snapshot ready).map Task.get).flatten
    let production := ((waveTasks width snapshot ready).map Task.get).flatten
    need s!"{label}, width {width}: projected tasks preserve complete ordered outcomes"
      (sameOutcomes explicit expected)
    need s!"{label}, width {width}: production uses equivalent outcomes"
      (sameOutcomes production expected)

private def checks (count : Nat) : Except String Unit := do
  let (snapshot, ready) := fixture count
  let projected := _root_.Ix.Compile.WorkerContext.project snapshot
  need "the fixture populates every output-only snapshot field"
    (!snapshot.nameToNamed.isEmpty && !snapshot.constants.isEmpty && snapshot.totalBytes != 0 &&
      !snapshot.ungrounded.isEmpty && !snapshot.blocks.isEmpty)
  need "projected tasks capture none of the driver's output-only fields"
    (projected.nameToNamed.isEmpty && projected.constants.isEmpty && projected.totalBytes == 0 &&
      projected.ungrounded.isEmpty && projected.blocks.isEmpty)
  compareTasks "mixed successful and failing blocks" snapshot ready
  compareTasks "empty task array" snapshot #[]
  let fallback := { snapshot with env := { consts := {}, fallback? := some snapshot.env.get? } }
  compareTasks "fallback source lookups" fallback ready
  let conflictingBlobs := ({} : Std.HashMap Address ByteArray).insert
    (Address.admissionHash "worker literal".toUTF8) "different payload".toUTF8
  let conflict := { snapshot with blobs := conflictingBlobs }
  compareTasks "ambient blob conflicts" conflict ready
  let tight := { snapshot with sharingLimits := { snapshot.sharingLimits with maxNodes := 0 } }
  compareTasks "sharing resource refusals" tight ready
  let some (literal, _, literalAll) := ready[0]? | throw "fixture is empty"
  need "ordinary literal block succeeds before changing its inputs" (runBlock snapshot literalAll literal).isOk
  need "projected workers retain ambient collision checks" (match runBlock conflict literalAll literal with
    | .error (.invalidMutualBlock "anonymous publication: conflicting blob payload") => true
    | _ => false)
  need "projected workers retain nondefault sharing limits" (match runBlock tight literalAll literal with
    | .error (.resourceLimit _) => true
    | _ => false)
  let some (reference, _, referenceAll) := ready[1]? | throw "fixture has no reference block"
  need "the address-map fixture resolves its external reference" (runBlock snapshot referenceAll reference).isOk
  need "dropping the required address map changes the refusal" (match runBlock
      { snapshot with nameToAddr := {} } referenceAll reference with
    | .error (.missingConstant _) => true
    | _ => false)

public def suite : List LSpec.TestSeq := [
  .individualIO "worker snapshot: exact tasks, retained reads and refusals" none (do
    let result ← IO.lazyPure fun _ => checks 269
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done
]

end Tests.Ix.Compile.WorkerSnapshot
