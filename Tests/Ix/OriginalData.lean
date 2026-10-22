module
public import Ix.Compile.OriginalData
public import LSpec

open Ix.Compile.OriginalData

private def checks (key : Address) : List (String × Bool) := Id.run do
  let label : Ix.Name := .anonymous key
  let knownNone : Receipt := {
    name := label, published := key, original := { addr := key, bytes := .empty }
    hints := some none, block? := some { addr := key, bytes := .empty } }
  let selected := fun (members : Array MemberShape) (index : Nat) (kind : ProjectionKind) =>
    requiresHint (({} : Std.HashMap Address Shape).insert key (.block members))
      label #[knownNone] (.projection key index kind)
  let members : Array MemberShape := #[.defn .thm, .indc 1, .recr]
  return [
    ("definition needs a hint", (requiresHint {} label #[] (.defn .defn)).toOption == some true),
    ("theorem permits known none", (requiresHint {} label #[] (.defn .thm)).toOption == some false),
    ("opaque permits known none", (requiresHint {} label #[] (.defn .opaq)).toOption == some false),
    ("definition projection needs a hint", (selected #[.defn .defn] 0 .defn).toOption == some true),
    ("theorem projection permits known none", (selected #[.defn .thm] 0 .defn).toOption == some false),
    ("opaque projection permits known none", (selected #[.defn .opaq] 0 .defn).toOption == some false),
    ("four valid projection variants", [(ProjectionKind.defn, 0), (.indc, 1), (.recr, 2), (.ctor 0, 1)].all
      (fun (kind, index) => (selected members index kind).toOption == some false)),
    ("four bad member indices", [ProjectionKind.defn, .indc, .recr, .ctor 0].all
      (fun kind => (selected members 3 kind).toOption.isNone)),
    ("four wrong member kinds", [(ProjectionKind.defn, 1), (.indc, 0), (.recr, 0), (.ctor 0, 0)].all
      (fun (kind, index) => (selected members index kind).toOption.isNone)),
    ("bad constructor index", (selected members 1 (.ctor 1)).toOption.isNone),
    ("missing mutual view", (requiresHint {} label #[knownNone] (.projection key 0 .indc)).toOption.isNone),
    ("missing captured block", (requiresHint {} label #[{ knownNone with block? := none }]
      (.projection key 0 .indc)).toOption.isNone)]

/-- Keep the fixture parameterized so no checks run at module initialization. -/
public def Tests.Ix.OriginalData.units (key : Address) : LSpec.TestSeq :=
  .individualIO "original finalization: declaration kinds and projection controls" none (do
    let rows ← IO.lazyPure fun _ => checks key
    return match rows.find? (!·.2) with
      | none => (true, rows.length, rows.length, none)
      | some (label, _) => (false, 0, rows.length, some label)) .done
