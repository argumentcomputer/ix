/-
  `ix diff <old.ixe> <new.ixe>`: structured diff of two serialized Ixon
  environments.

  The diff itself is computed in Rust (`rs_diff_env_files` →
  `ixon::diff`): both files are memory-mapped and lazily parsed
  (constant windows stay zero-copy mmap slices; `ConstantMeta` is never
  bulk-materialized) and compared on anonymous structure — names serve
  as join/display keys, constants compare by content address with
  per-field classification (type/value/lvls/…, `block.*` for projection
  targets, `"encoding"` when only the representation moved). `--meta`
  additionally compares named metadata (`ConstantMeta`/`original`) via
  a streaming merge-join over both files' §5 named sections.

  Every changed row carries a root-vs-rippled verdict: one edited
  constant re-addresses its whole reverse-dependency cone, so most
  changed rows are *rippled* (fully explained by dependency
  re-addressing) and only the *roots* are intrinsic edits. The default
  display lists roots and summarizes the rippled count; `--verbose`
  lists rippled rows too, and in `--meta` mode rippled rows carrying
  metadata edits stay visible.

  Exit codes (GNU diff convention): 0 = no difference found in the
  selected mode, 1 = differences found, 2 = error.
-/
module
public import Cli
public import Ix.Address
public import Ix.Common
public import Ix.Ixon

public section

namespace Ix.Cli.DiffCmd

private def pad (s : String) (w : Nat) : String :=
  s.pushn ' ' (w - s.length)

private def shortAddr (verbose : Bool) (a : Address) : String :=
  if verbose then toString a else ((toString a).take 12).toString ++ "…"

/-- Synthetic mutual-block names embed the block hash as their second
    component (`Ix.<64-hex>.…`); a changed block churns one such pair
    per block, so the default display groups them into a count. -/
private def isSyntheticMuts (s : String) : Bool :=
  match s.splitOn "." with
  | "Ix" :: h :: _ =>
    h.length == 64 && h.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')
  | _ => false

private def printStats (path : String) (s : Ixon.EnvStats) : IO Unit :=
  IO.println
    s!"[diff] {path}: {s.consts} consts, {s.named} named, {s.blobs} blobs, {s.comms} comms"

/-- Print up to `cap` addresses (all when `verbose`), one per line. -/
private def printAddrList
    (linePrefix : String) (addrs : Array Address) (verbose : Bool) :
    IO Unit := do
  let cap := if verbose then addrs.size else min addrs.size 10
  for a in addrs[0:cap] do
    IO.println s!"{linePrefix}{shortAddr verbose a}"
  if addrs.size > cap then
    IO.println s!"{linePrefix}… and {addrs.size - cap} more"

private def brackets (labels : Array String) : String :=
  "[" ++ ", ".intercalate labels.toList ++ "]"

private def printNamedSection
    (d : Ixon.EnvDiff) (wantMeta verbose : Bool) : IO Unit := do
  let keep (s : String) : Bool := verbose || !isSyntheticMuts s
  let added := d.namedAdded.filter (keep ·.1)
  let removed := d.namedRemoved.filter (keep ·.1)
  let synAdded := d.namedAdded.size - added.size
  let synRemoved := d.namedRemoved.size - removed.size
  let roots := d.namedChanged.filter (!·.rippled)
  let rippleCount :=
    if d.namedChanged.isEmpty then ""
    else s!" ({roots.size} roots, {d.namedChanged.size - roots.size} rippled)"
  let metaCount :=
    if wantMeta then s!", {d.namedMetaOnly.size} metadata-only" else ""
  IO.println
    s!"named: {d.namedAdded.size} added, {d.namedRemoved.size} removed, {d.namedChanged.size} changed{rippleCount}{metaCount}"
  if synAdded + synRemoved > 0 then
    IO.println
      s!"  (synthetic mutual-block names: {synAdded} added, {synRemoved} removed — --verbose lists)"
  -- Changed rows shown by default: the roots, plus (under --meta)
  -- rippled rows carrying metadata edits — `namedMetaOnly` only covers
  -- same-addr rows, so hiding those would hide real metadata changes.
  let shown := d.namedChanged.filter fun c =>
    verbose || !c.rippled || (wantMeta && !c.metaFields.isEmpty)
  -- Column width over everything we are about to print.
  let mut wMax := 0
  for (n, _) in added do wMax := max wMax n.length
  for (n, _) in removed do wMax := max wMax n.length
  for c in shown do wMax := max wMax c.name.length
  for (n, _) in d.namedMetaOnly do wMax := max wMax n.length
  let w := min wMax 40
  for (n, addr) in added do
    IO.println s!"  + {pad n w}  {shortAddr verbose addr}"
  for (n, addr) in removed do
    IO.println s!"  - {pad n w}  {shortAddr verbose addr}"
  for c in shown do
    let kind :=
      if c.oldKind == c.newKind then c.oldKind
      else s!"{c.oldKind}→{c.newKind}"
    let ripTag := if c.rippled then " (rippled)" else ""
    IO.println
      s!"  ~ {pad c.name w}  {pad kind 9}  {shortAddr verbose c.oldAddr} → {shortAddr verbose c.newAddr}  {brackets c.fields}{ripTag}"
    if wantMeta && !c.metaFields.isEmpty then
      IO.println s!"      meta: {brackets c.metaFields}"
  let hidden := d.namedChanged.size - shown.size
  if hidden > 0 then
    IO.println
      s!"  ({hidden} rippled rows hidden — address changes fully explained by dependency re-addressing; --verbose lists)"
  for (n, labels) in d.namedMetaOnly do
    IO.println s!"  m {pad n w}  {brackets labels}"
  if shown.any (·.fields.contains "encoding") then
    IO.println
      "  (encoding = representation changed; no semantic field difference detected)"

def runDiffCmd (p : Cli.Parsed) : IO UInt32 := do
  let some oldArg := p.positionalArg? "old"
    | p.printError "error: must specify <old.ixe> <new.ixe>"; return 2
  let some newArg := p.positionalArg? "new"
    | p.printError "error: must specify <old.ixe> <new.ixe>"; return 2
  let oldPath := oldArg.as! String
  let newPath := newArg.as! String
  let wantMeta := p.hasFlag "meta"
  if wantMeta && p.hasFlag "anon" then
    IO.eprintln "error: --anon and --meta are mutually exclusive"
    return 2
  let verbose := p.hasFlag "verbose"
  -- Byte-equal fast path and the diff itself both run over mmapped
  -- files — nothing is read into Lean ByteArrays.
  let d ← try
    if ← Ixon.rsIxeFilesEqual oldPath newPath then
      IO.println "identical"
      return (0 : UInt32)
    Ixon.rsDiffEnvFiles oldPath newPath wantMeta
  catch e =>
    IO.eprintln s!"error: {e.toString}"
    return (2 : UInt32)
  printStats oldPath d.statsA
  printStats newPath d.statsB
  if d.isEmpty then
    if wantMeta then
      IO.println "files differ in bytes but no semantic difference found"
    else
      IO.println
        "files differ in bytes but no anonymous-structure difference found (try --meta)"
    return 0
  if let some (oldMain, newMain) := d.mainChanged then
    let fmt : Option Address → String
      | none => "∅"
      | some a => shortAddr verbose a
    IO.println s!"main: {fmt oldMain} → {fmt newMain}"
  unless d.assumptionsAdded.isEmpty && d.assumptionsRemoved.isEmpty do
    IO.println
      s!"assumptions: +{d.assumptionsAdded.size} −{d.assumptionsRemoved.size}"
    printAddrList "  + " d.assumptionsAdded verbose
    printAddrList "  - " d.assumptionsRemoved verbose
  unless d.namedAdded.isEmpty && d.namedRemoved.isEmpty
      && d.namedChanged.isEmpty && d.namedMetaOnly.isEmpty do
    printNamedSection d wantMeta verbose
  unless d.commsAdded.isEmpty && d.commsRemoved.isEmpty
      && d.commsChanged.isEmpty do
    IO.println
      s!"comms: +{d.commsAdded.size} −{d.commsRemoved.size} ~{d.commsChanged.size}"
    printAddrList "  + " d.commsAdded verbose
    printAddrList "  - " d.commsRemoved verbose
    printAddrList "  ~ " d.commsChanged verbose
  unless d.constsOnlyA.isEmpty && d.constsOnlyB.isEmpty do
    let note :=
      if verbose then "" else " (mutual blocks/projections; --verbose lists)"
    IO.println
      s!"consts: {d.constsOnlyA.size} only in {oldPath}, {d.constsOnlyB.size} only in {newPath}{note}"
    if verbose then
      printAddrList "  - " d.constsOnlyA verbose
      printAddrList "  + " d.constsOnlyB verbose
  unless d.blobsOnlyA.isEmpty && d.blobsOnlyB.isEmpty do
    IO.println
      s!"blobs: {d.blobsOnlyA.size} only in {oldPath}, {d.blobsOnlyB.size} only in {newPath}"
    if verbose then
      printAddrList "  - " d.blobsOnlyA verbose
      printAddrList "  + " d.blobsOnlyB verbose
  unless d.hintsChanged.isEmpty do
    IO.println s!"hints changed: {d.hintsChanged.size}"
    let cap := if verbose then d.hintsChanged.size else min d.hintsChanged.size 10
    for (a, oldH, newH) in d.hintsChanged[0:cap] do
      IO.println s!"  {shortAddr verbose a}  {oldH} → {newH}"
    if d.hintsChanged.size > cap then
      IO.println s!"  … and {d.hintsChanged.size - cap} more"
  IO.println s!"[diff] {oldPath} ≠ {newPath}"
  return 1

end Ix.Cli.DiffCmd

open Ix.Cli.DiffCmd in
def diffCmd : Cli.Cmd := `[Cli|
  diff VIA runDiffCmd;
  "Print a structured diff of two serialized Ixon environments (`.ixe`). By default only anonymous structure is compared: constants by content address (joined through names, with per-field change classification), consts/blobs sets, comms, main/assumptions, and reducibility hints. Changed names are root-caused: rows fully explained by dependency re-addressing are counted as `rippled` and hidden by default, so the listing shows the intrinsic edits (roots). Exit codes: 0 = no difference, 1 = differences found, 2 = error."

  FLAGS:
    anon; "Compare only anonymous structure (the default; accepted for explicitness)."
    «meta»; "Additionally compare named metadata (binder names, originals, kv-maps)."
    verbose; "Print full addresses, uncapped lists, synthetic mutual-block names, and rippled changed rows."

  ARGS:
    old : String; "Path to the first (old) serialized env (`.ixe`)."
    new : String; "Path to the second (new) serialized env (`.ixe`)."
]

end
