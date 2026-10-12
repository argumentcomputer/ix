import LSpec
import Ix.CompileM

/-! Supplied conflicting stores exercise local compatibility checks. These
controls do not claim a cryptographic collision or a valid-source miscompile. -/

namespace Tests.Ix.Compile.LocalBlob

open LSpec
open _root_.Ix (Name Expr Level)
open _root_.Ix.CompileM

private def raw (action : CompileM α) (state : BlockState := {})
    (env : CompileEnv := default) : Except CompileError α × BlockState :=
  (action (env, { all := {}, current := Name.mkAnon, mutCtx := default, univCtx := [] })).run state

private def conflict (result : Except CompileError α) : Bool := match result with
  | .error (.invalidMutualBlock "anonymous publication: conflicting blob payload") => true
  | _ => false

def controls : List (String × Bool) := Id.run do
  let bytes := "new".toUTF8
  let old := "old".toUTF8
  let address := Address.blake3 bytes
  let poisoned : BlockState := { blockBlobs := ({} : Std.HashMap Address ByteArray).insert address old }
  let prior : CompileEnv := { (default : CompileEnv) with blobs := poisoned.blockBlobs }
  let matching : CompileEnv := { (default : CompileEnv) with blobs := ({} : Std.HashMap Address ByteArray).insert address bytes }
  let (localResult, localAfter) := raw (storeString "new") poisoned
  let (ambientResult, ambientAfter) := raw (storeString "new") {} prior
  let (accepted, acceptedAfter) := raw (storeString "new") {} matching
  let (aliasResult, aliasAfter) := raw (storeString "new") acceptedAfter matching
  let (hiddenConflict, hiddenAfter) := raw (storeString "new") acceptedAfter prior
  let name := Name.fromLeanName `LocalBlob.new
  let (nameResult, nameAfter) := raw (compileName name) poisoned
  let (retryResult, retryAfter) := raw (compileName name) nameAfter
  let (namesResult, namesAfter) := raw (compileNames #[Name.fromLeanName `Safe, name]) poisoned
  let (parentResult, parentAfter) := raw (compileName (Name.fromLeanName `new.child)) poisoned
  let literal := Expr.mkLit (.strVal "new")
  let (direct, directAfter) := raw (compileExprPartial literal) poisoned
  let (reference, referenceAfter) := raw (compileExprTotalFuel (exprCompileDepth literal) literal) poisoned
  let (structural, structuralAfter) := raw (collectExprTables literal default (#[], #[], {})) poisoned
  let (worklist, worklistAfter) := raw (collectExprTablesWorklist literal default (#[], #[], {})) poisoned
  let (datum, datumAfter) := raw (compileDataValue (.ofString "new")) poisoned
  let natural := ByteArray.mk (Nat.toBytesLE 42)
  let naturalAddress := Address.blake3 natural
  let naturalPoisoned : BlockState := {
    blockBlobs := ({} : Std.HashMap Address ByteArray).insert naturalAddress old }
  let (natResult, natAfter) := raw (compileExprPartial (Expr.mkLit (.natVal 42))) naturalPoisoned
  let (natDatum, natDatumAfter) := raw (compileDataValue (.ofNat 42)) naturalPoisoned
  let (intDatum, intAfter) := raw (compileDataValue (.ofInt (.negSucc 41))) {
    blockBlobs := ({} : Std.HashMap Address ByteArray).insert (Address.blake3 (serializeIxInt (.negSucc 41))) old }
  let syntaxAddress := Address.blake3 (ByteArray.mk #[0])
  let (syntaxDatum, syntaxAfter) := raw (compileDataValue (.ofSyntax .missing)) {
    blockBlobs := ({} : Std.HashMap Address ByteArray).insert syntaxAddress old }
  return [
    ("local conflict is rejected without replacement", conflict localResult && localAfter.blockBlobs.get? address == some old),
    ("ambient conflict is rejected before shadowing", conflict ambientResult && ambientAfter.blockBlobs.isEmpty),
    ("identical ambient payload is accepted", accepted.toOption == some address && acceptedAfter.blockBlobs.get? address == some bytes),
    ("identical local payload is accepted", aliasResult.toOption == some address && aliasAfter.blockBlobs.size == 1),
    ("matching local payload cannot hide ambient conflict", conflict hiddenConflict && hiddenAfter.blockBlobs.get? address == some bytes),
    ("name metadata cannot overwrite literal data", conflict nameResult && nameAfter.blockBlobs.get? address == some old),
    ("failed name leaves no cache entry masking a retry", nameAfter.blockNames.isEmpty && conflict retryResult && retryAfter.blockNames.isEmpty),
    ("array of names commits only after all checks", conflict namesResult && namesAfter.blockNames.isEmpty && namesAfter.blockBlobs.size == 1),
    ("ancestor conflict rolls back earlier child writes", conflict parentResult && parentAfter.blockNames.isEmpty && parentAfter.blockBlobs.size == 1),
    ("direct expression path preserves the conflicting payload", conflict direct && directAfter.blockBlobs.get? address == some old),
    ("reference expression path also refuses", conflict reference && referenceAfter.blockBlobs.get? address == some old),
    ("failed literal is not cached or allocated", directAfter.exprCache.isEmpty && directAfter.arena.nodes.isEmpty),
    ("structural preseed walk refuses", conflict structural && structuralAfter.blockBlobs.get? address == some old),
    ("runtime worklist preseed walk refuses", conflict worklist && worklistAfter.blockBlobs.get? address == some old),
    ("string metadata uses the same guard", conflict datum && datumAfter.blockBlobs.get? address == some old),
    ("natural literal uses the same guard", conflict natResult && natAfter.blockBlobs.get? naturalAddress == some old),
    ("natural metadata uses the same guard", conflict natDatum && natDatumAfter.blockBlobs.get? naturalAddress == some old),
    ("integer metadata uses the same guard", conflict intDatum && intAfter.blockBlobs.size == 1),
    ("syntax metadata uses the same guard", conflict syntaxDatum && syntaxAfter.blockBlobs.get? syntaxAddress == some old)]

def suite : List TestSeq := controls.map fun (label, ok) => test s!"local blob: {label}" ok

end Tests.Ix.Compile.LocalBlob
