import Tests.Ix.SourceContract.CopyFixture
import Ix.Compile.SourceContract.Transport

/-! Marker hygiene (R18): copies of a marker annotate nothing, originals keep
their sites, transport strips copies, and conflicting or orphaned copies are
still rejected. -/

open Lean Ix.Compile

namespace Tests.Ix.SourceContract.CopyCheck

def hasMarker (expr : Expr) : Bool :=
  (expr.find? fun
    | .mdata data _ => hasSourceAnnotation data
    | _ => false).isSome

end Tests.Ix.SourceContract.CopyCheck

open Tests.Ix.SourceContract.CopyCheck in
run_cmd do
  let root := `Tests.Ix.SourceContract.CopyFixture
  let names := #[root ++ `passesNumeral, root ++ `vhead, root ++ `vhead.match_1,
    root ++ `countdown, root ++ `countdown._unary, root ++ `viaLet, root ++ `viaLet.match_1,
    root ++ `viaBorrow, root ++ `viaBorrow.match_1]
  let selected ← names.toList.mapM fun name => do return (name, ← getConstInfo name)
  -- Every selected declaration either carries markers or a registration, and
  -- all of them resolve: copies no longer fail as misplaced or mismatched.
  let input ← match compileInputFromEnv (← getEnv) selected with
    | .ok input => pure input
    | .error error => throwError "copy fixtures do not export: {error}"
  let resolved ← match input.resolve with
    | .ok resolved => pure resolved
    | .error error => throwError "copy fixtures do not resolve: {error}"
  let bindersOf (name : Name) : Array ResolvedBinderContract :=
    ((resolved.contracts.find? (·.source.name == name)).map (·.binders)).getD #[]
  -- Copies in callers, matchers, and packed domains annotate nothing.
  for name in [root ++ `passesNumeral, root ++ `vhead.match_1, root ++ `countdown._unary,
      root ++ `viaLet.match_1, root ++ `viaBorrow.match_1] do
    unless (bindersOf name).isEmpty do throwError "a marker copy annotated a binder of {name}"
  -- The originals keep exactly their own sites.
  let vhead := bindersOf (root ++ `vhead)
  unless vhead.size == 4 && vhead.all (·.uses == .erased) do
    throwError "vhead lost or gained erased binder sites: {vhead.size}"
  let countdown := bindersOf (root ++ `countdown)
  unless countdown.size == 2 && countdown.all (·.uses == .erased) do
    throwError "countdown lost its erased proof binder: {countdown.size}"
  let viaLet := bindersOf (root ++ `viaLet)
  unless viaLet.size == 1 && viaLet.all (fun b => b.kind == .letE && b.letKind == .value &&
      b.value == .localShared) do
    throwError "viaLet lost its local let contract"
  let viaBorrow := bindersOf (root ++ `viaBorrow)
  unless viaBorrow.size == 1 && viaBorrow.all (fun b => b.kind == .letE &&
      b.letKind == .borrowShared) do
    throwError "viaBorrow lost its borrow contract"
  -- Transport strips every copy; a caller with only copies is ordinary source.
  let prepared ← match input.prepare with
    | .ok prepared => pure prepared
    | .error error => throwError "copy fixtures do not transport: {error}"
  for (name, source) in prepared do
    for expr in [source.type] ++ (sourceBody? source).toList do
      if hasMarker expr then throwError "transport kept a source marker copy in {name}"
  let some (_, caller) := prepared.find? (·.1 == root ++ `passesNumeral)
    | throwError "caller missing after transport"
  if sourceHasSemanticContracts caller then
    throwError "a caller gained semantic contracts from a copied marker"

-- A copy that disagrees with its original is still rejected, and an original
-- that survives only as copies is reported instead of silently dropped.
run_cmd do
  let nat : Expr := .const ``Nat []
  let original : BinderAnnotation := { origin := 7, binder := `x, uses := .linear, value := .unique }
  let copy : BinderAnnotation := { original with uses := .affine }
  let source : ConstantInfo := .defnInfo {
    name := `conflicting, levelParams := []
    type := .forallE `x (.mdata original.toMetadata nat) nat .default
    value := .lam `x nat (.mdata copy.toMetadata (.bvar 0)) .default
    hints := .abbrev, safety := .safe, all := [`conflicting] }
  match SourceContract.fromAnnotations source with
  | .error (.conflictingAnnotation `conflicting _) => pure ()
  | other => throwError "a conflicting copy was accepted: {repr (other.map (·.binders.size))}"
  -- The marker on `y`'s domain names another binder: alone, it is only a copy.
  let orphan : ConstantInfo := .defnInfo {
    name := `orphan, levelParams := []
    type := .forallE `y (.mdata original.toMetadata nat) nat .default
    value := .lam `y nat (.bvar 0) .default
    hints := .abbrev, safety := .safe, all := [`orphan] }
  match SourceContract.fromAnnotations orphan with
  | .ok contract => unless contract.binders.isEmpty do throwError "a renamed copy annotated a binder"
  | .error error => throwError "a foreign copy was rejected: {error}"
  match checkAnnotationsSurvive `orphan #[orphan] 0 100 with
  | .error (.lostAnnotation `orphan 7 `x) => pure ()
  | _ => throwError "an original that survives only as a copy was not reported"
  -- Copies of markers written outside the command are not this command's loss.
  unless (checkAnnotationsSurvive `orphan #[orphan] 8 100).isOk do
    throwError "a foreign copy was reported as a lost annotation"
