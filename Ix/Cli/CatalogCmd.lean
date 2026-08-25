/-
  `ix catalog`: assemble, verify, and inspect `.ixc` catalog manifests
  over anonymous `.ixe` pieces — pure artifact algebra.

  A catalog is semantically ONE anonymous env (the union of its
  members' constant sets), committed by two roots: `members_root`
  (canonical merkle root over member env roots) and `content_root`
  (canonical root over the union's constant addresses — the env root
  of the virtual union env). Anonymous Ixon is conflict-free, so no
  qualification, relocation, or union import exists anywhere behind
  these verbs: the Rust core (`crates/ixon/src/catalog.rs`, via
  `crates/ffi/src/catalog.rs`) reads piece HEADERS and sorted §2
  address lists, hashes files, and writes the manifest — O(pieces)
  resident, never a materialized union, and never a Lean frontend.

  Compilation orchestration deliberately does NOT live here (no
  `ix catalog build`): drivers like `truthmines` own the per-member
  `ix compile` loop; these verbs stay reusable by any project.

  On disk a `.ixc` is a self-contained DIRECTORY — manifest and piece
  files together, no separate pieces dir:

    <name>.ixc/
      manifest        the binary manifest
      <label>.ixe     one piece per member (label = filename stem,
                      validated filename-safe by the Rust core)

  `assemble` ingests external pieces by hard link (copy fallback), so
  assembling from same-filesystem pieces moves no bytes. No JSON (or
  other) report artifacts are written anywhere in this flow: the
  manifest IS the machine-readable record (`ix catalog info` dumps
  it), and the FFI's JSON strings are an in-memory carrier only.
-/
module
public import Cli
public import Ix.Common

public section

namespace Ix.Cli.CatalogCmd

@[extern "rs_catalog_assemble"]
opaque rsCatalogAssembleFFI : @& String → @& String → IO String

@[extern "rs_catalog_verify"]
opaque rsCatalogVerifyFFI : @& String → Bool → IO String

@[extern "rs_catalog_info"]
opaque rsCatalogInfoFFI : @& String → IO String

/-- Split a comma list, dropping empties. -/
private def commaList (s : String) : List String :=
  (s.splitOn ",").filter (!·.isEmpty)

/-- Parse `--deps "1:0;2:0,1"`: per-member dependency indices, entries
    `member:dep,dep` separated by `;`. Members not listed have no
    deps. -/
private def parseDeps (raw : String) (memberCount : Nat) :
    Except String (Array (List Nat)) := do
  let mut deps : Array (List Nat) := .replicate memberCount []
  for entry in (raw.splitOn ";").filter (!·.isEmpty) do
    match entry.splitOn ":" with
    | [idxS, depsS] =>
      let some idx := idxS.toNat?
        | throw s!"--deps: bad member index `{idxS}`"
      unless idx < memberCount do
        throw s!"--deps: member index {idx} out of range ({memberCount} pieces)"
      let mut ds : List Nat := []
      for d in commaList depsS do
        let some dn := d.toNat?
          | throw s!"--deps: bad dep index `{d}`"
        unless dn < idx do
          throw s!"--deps: member {idx} depends on {dn}, which is not \
strictly before it (topo order, deps first)"
        ds := ds ++ [dn]
      deps := deps.set! idx ds
    | _ => throw s!"--deps: bad entry `{entry}` (want `member:dep,dep`)"
  return deps

/-- Per-piece metadata from a comma-list flag: one value for all
    pieces, exactly one per piece, or absent (default). Empty entries
    are MEANINGFUL here (a local member's pin is empty), so the list
    is split verbatim, not filtered. -/
private def perPiece (p : Cli.Parsed) (flag : String) (n : Nat)
    (dflt : String) : Except String (Array String) :=
  match (p.flag? flag).map (·.as! String) with
  | none => .ok (.replicate n dflt)
  | some raw =>
    let xs := raw.splitOn ","
    if xs.length == 1 then .ok (.replicate n xs[0]!)
    else if xs.length == n then .ok xs.toArray
    else .error s!"--{flag}: {xs.length} values for {n} pieces"

def runAssemble (p : Cli.Parsed) : IO UInt32 := do
  let some outArg := p.positionalArg? "out"
    | p.printError "error: must specify the output .ixc path"
      return 1
  let out := outArg.as! String
  let pieces := (p.variableArgsAs! String).toList
  if pieces.isEmpty then
    p.printError "error: at least one piece .ixe is required"
    return 1
  let n := pieces.length
  let labels ← do
    let dflt := pieces.map fun path =>
      (System.FilePath.mk path).fileStem.getD path
    match (p.flag? "labels").map (·.as! String) with
    | none => pure dflt.toArray
    | some raw =>
      let xs := commaList raw
      unless xs.length == n do
        p.printError s!"error: --labels: {xs.length} values for {n} pieces"
        return 1
      pure xs.toArray
  let toolchains ← match perPiece p "toolchains" n Lean.versionString with
    | .ok xs => pure xs
    | .error e => p.printError s!"error: {e}"; return 1
  let pins ← match perPiece p "pins" n "" with
    | .ok xs => pure xs
    | .error e => p.printError s!"error: {e}"; return 1
  let deps ← match parseDeps ((p.flag? "deps").map (·.as! String) |>.getD "") n with
    | .ok ds => pure ds
    | .error e => p.printError s!"error: {e}"; return 1
  let members := Lean.Json.arr <| (pieces.zipIdx.map fun (path, i) =>
    Lean.Json.mkObj
      [ ("path", Lean.Json.str path)
      , ("label", Lean.Json.str labels[i]!)
      , ("toolchain", Lean.Json.str toolchains[i]!)
      , ("sourcePin", Lean.Json.str pins[i]!)
      , ("deps", Lean.Json.arr (deps[i]!.toArray.map (Lean.toJson ·))) ]).toArray
  let summary ← rsCatalogAssembleFFI out members.compress
  match Lean.Json.parse summary with
  | .ok json =>
    let field (k : String) : String :=
      ((json.getObjVal? k).bind (·.getStr?)).toOption.getD "?"
    let num (k : String) : String :=
      match (json.getObjVal? k).toOption with
      | some v => v.compress | none => "?"
    IO.println s!"[catalog] {n} member(s) → {out} (manifest {num "bytes"} bytes)"
    IO.println s!"[catalog] members_root {field "membersRoot"}"
    IO.println s!"[catalog] content_root {field "contentRoot"}"
  | .error _ => IO.println summary
  return 0

def runVerify (p : Cli.Parsed) : IO UInt32 := do
  let some ixcArg := p.positionalArg? "ixc"
    | p.printError "error: must specify the .ixc directory"
      return 1
  let ixc := ixcArg.as! String
  let deep := p.hasFlag "deep"
  let summary ← rsCatalogVerifyFFI ixc deep
  match Lean.Json.parse summary with
  | .ok json =>
    let field (k : String) : String :=
      ((json.getObjVal? k).bind (·.getStr?)).toOption.getD "?"
    let num (k : String) : String :=
      match (json.getObjVal? k).toOption with
      | some v => v.compress | none => "?"
    IO.println s!"[catalog] OK: {num "members"} member(s), \
{num "unionConsts"} union constants ({field "profile"}\
{if deep then ", deep" else ""})"
    IO.println s!"[catalog] members_root {field "membersRoot"}"
    IO.println s!"[catalog] content_root {field "contentRoot"}"
  | .error _ => IO.println summary
  return 0

def runInfo (p : Cli.Parsed) : IO UInt32 := do
  let some ixcArg := p.positionalArg? "ixc"
    | p.printError "error: must specify the .ixc path"
      return 1
  let summary ← rsCatalogInfoFFI (ixcArg.as! String)
  match Lean.Json.parse summary with
  | .ok json => IO.println json.pretty
  | .error _ => IO.println summary
  return 0

def catalogAssembleCmd : Cli.Cmd := `[Cli|
  assemble VIA runAssemble;
  "Assemble a self-contained fat-profile .ixc DIRECTORY from piece .ixe files (topo order, dependencies first): pieces are ingested as <label>.ixe (hard link or copy; paths already inside are untouched) and the manifest is written at <out>/manifest. Reads only piece headers and §2 address lists — no Lean frontend, no materialized union, no report artifacts."

  FLAGS:
    labels : String; "Comma-separated member labels, one per piece (default: file stems). The label is the piece's filename stem inside the .ixc directory."
    toolchains : String; "Comma-separated toolchains, one per piece or a single value for all (default: this binary's Lean version)."
    pins : String; "Comma-separated source pins, one per piece or a single value for all (e.g. `git:<url>@<rev>`; empty entries mean local)."
    deps : String; "Member dependency indices, `member:dep,dep` entries separated by `;` (e.g. `1:0;2:0,1`). Indices must be strictly before the member (topo order)."

  ARGS:
    out : String; "Output .ixc directory (manifest written fail-closed: .tmp + atomic rename)."
    ...pieces : String; "Piece .ixe files, topo order (dependencies first)."
]

def catalogVerifyCmd : Cli.Cmd := `[Cli|
  verify VIA runVerify;
  "Verify a self-contained .ixc directory: both roots recomputed (members from entries, content by the k-way sweep over the pieces inside), every piece's env root, const count, and size checked; chunked profiles enforce the no-redeclaration invariant. --deep re-hashes files and fully loads each piece (per-constant blake3)."

  FLAGS:
    deep; "Also re-hash every file against the manifest and fully verify each piece load."

  ARGS:
    ixc : String; "Path to the .ixc directory."
]

def catalogInfoCmd : Cli.Cmd := `[Cli|
  info VIA runInfo;
  "Print a .ixc directory's manifest (members, roots, storage). Touches no piece files; members_root is still recomputed on load."

  ARGS:
    ixc : String; "Path to the .ixc directory."
]

def runCatalog (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.CatalogCmd

open Ix.Cli.CatalogCmd in
def catalogCmd : Cli.Cmd := `[Cli|
  catalog VIA runCatalog;
  "Assemble, verify, and inspect .ixc catalog manifests over anonymous .ixe pieces"

  SUBCOMMANDS:
    catalogAssembleCmd;
    catalogVerifyCmd;
    catalogInfoCmd
]

end
