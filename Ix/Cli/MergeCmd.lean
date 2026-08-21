/-
  `ix merge`: materialize the anonymous union of `.ixe` pieces as ONE
  ordinary v1 `.ixe` env — the derived single-file view of a catalog
  (subset). Never the source of truth: the `.ixc` manifest is; this
  exists for consumers that want one file (`import_ixe` inputs,
  single-artifact checking, distribution).

  Anonymous union is trivial and conflict-free: §2 is content-
  addressed, so the k-way merge over the pieces' already-sorted §2
  lists dedups by construction, with every unique constant's bytes
  blake3-verified against its address before re-emission (fail closed
  on a corrupt input). Blobs union; §3 hints min-merge
  (order-independent); `assumptions` = union ∖ carried; `main` kept
  only if unique across inputs. Output §4/§5/§6 are empty — the
  merged env is strictly anonymous.

  Inputs come either as explicit piece paths or from a `.ixc`
  directory (`--ixc`, optionally `--only`-filtered by label; a `.ixc`
  is self-contained, so pieces resolve inside it as
  `<cat.ixc>/<label>.ixe`).
-/
module
public import Cli
public import Ix.Common
public import Ix.Cli.CatalogCmd

public section

namespace Ix.Cli.MergeCmd

@[extern "rs_merge_anon"]
opaque rsMergeAnonFFI : @& String → @& String → IO String

def runMerge (p : Cli.Parsed) : IO UInt32 := do
  let some outArg := p.positionalArg? "out"
    | p.printError "error: must specify the output .ixe path"
      return 1
  let out := outArg.as! String
  let explicitPieces := (p.variableArgsAs! String).toList
  let ixc? := (p.flag? "ixc").map (·.as! String)
  let pieces : List String ← match ixc?, explicitPieces with
    | none, [] =>
      p.printError "error: give piece .ixe files or --ixc <cat.ixc>"
      return 1
    | none, ps => pure ps
    | some _, _ :: _ =>
      p.printError "error: --ixc and explicit piece paths are mutually exclusive"
      return 1
    | some ixc, [] => do
      -- Resolve members from the manifest: the .ixc is self-contained,
      -- label → <ixc>/<label>.ixe.
      let summary ← Ix.Cli.CatalogCmd.rsCatalogInfoFFI ixc
      let json ← match Lean.Json.parse summary with
        | .ok j => pure j
        | .error e => throw <| IO.userError s!"merge: bad catalog info JSON: {e}"
      let members ← match (json.getObjVal? "members").bind (·.getArr?) with
        | .ok ms => pure ms
        | .error e => throw <| IO.userError s!"merge: {e}"
      let dir := ixc
      let only : Option (List String) := (p.flag? "only").map fun f =>
        ((f.as! String).splitOn ",").filter (!·.isEmpty)
      let mut labels : List String := []
      for m in members do
        let label ← match (m.getObjVal? "label").bind (·.getStr?) with
          | .ok l => pure l
          | .error e => throw <| IO.userError s!"merge: member without label: {e}"
        labels := labels ++ [label]
      if let some wanted := only then
        for w in wanted do
          unless labels.contains w do
            throw <| IO.userError s!"merge: --only names `{w}`, which is \
not a member label of {ixc} (members: {labels})"
      let selected := match only with
        | none => labels
        | some wanted => labels.filter wanted.contains
      pure <| selected.map fun l => s!"{dir}/{l}.ixe"
  let piecesJson := Lean.Json.arr (pieces.toArray.map Lean.Json.str)
  let summary ← rsMergeAnonFFI out piecesJson.compress
  match Lean.Json.parse summary with
  | .ok json =>
    let field (k : String) : String :=
      ((json.getObjVal? k).bind (·.getStr?)).toOption.getD "?"
    let num (k : String) : String :=
      match (json.getObjVal? k).toOption with
      | some v => v.compress | none => "?"
    IO.println s!"[merge] {pieces.length} piece(s) → {out}: \
{num "consts"} constants, {num "blobs"} blobs, {num "bytes"} bytes"
    IO.println s!"[merge] root {field "root"}"
  | .error _ => IO.println summary
  return 0

end Ix.Cli.MergeCmd

open Ix.Cli.MergeCmd in
def mergeCmd : Cli.Cmd := `[Cli|
  merge VIA runMerge;
  "Materialize the anonymous union of .ixe pieces as one ordinary .ixe (derived view; the .ixc stays the source of truth)"

  FLAGS:
    ixc : String; "Merge a .ixc directory's members instead of explicit paths (self-contained: pieces resolve as <cat.ixc>/<label>.ixe)."
    only : String; "With --ixc: comma-separated member labels to merge (default: all members)."

  ARGS:
    out : String; "Output .ixe path (written fail-closed: .tmp + atomic rename)."
    ...pieces : String; "Piece .ixe files to merge (omit when using --ixc)."
]

end
