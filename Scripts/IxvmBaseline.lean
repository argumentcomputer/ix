import Lean
import Ix.Aiur.Statistics

/-!
IxVM cost baseline runner, extractor, differ, and inspector.
Replaces `tools/ixvm/baseline/run.sh` and `tools/ixvm/baseline/baseline.py`.

Run from the repository root:

```sh
lake env lean --run Scripts/IxvmBaseline.lean run OUT [RECORDED]
lake env lean --run Scripts/IxvmBaseline.lean extract OUTDIR LOG [LOG ...] [--out BASE.ixb]
lake env lean --run Scripts/IxvmBaseline.lean diff OLD NEW [--top N]
lake env lean --run Scripts/IxvmBaseline.lean show BASE LABEL [--top N]
lake env lean --run Scripts/IxvmBaseline.lean --self-test
```

Snapshots use a compact typed binary format (`IXBL` v1, `.ixb`); `diff` and
`show` also accept legacy `.json` baseline files for comparison against older
recordings. Circuit FFT costs are computed directly with `Ix.Aiur.Statistics`
(`Aiur.fftCost`, `Aiur.computeStats`, `Aiur.ExecutionStats.roundedFftCost`).
-/

namespace IxvmBaseline

open Lean System

def usage : String :=
  "usage: lake env lean --run Scripts/IxvmBaseline.lean <command> [args...]\n\n" ++
  "Commands:\n" ++
  "  run OUT [RECORDED]                      Build, export, run pinned/bench/corpus suites,\n" ++
  "                                          write OUT/baseline.ixb (and OUT/diff.txt if RECORDED).\n" ++
  "                                          Honors BENCH=0 (skip ixvm-ind-decl-bench) and CORPUS=1.\n" ++
  "  extract OUTDIR LOG [LOG ...] [--out F]  Extract costs from *.stats.json sidecars and logs.\n" ++
  "                                          Writes binary .ixb to F (or stdout if --out omitted).\n" ++
  "  diff OLD NEW [--top N]                  Compare two baselines (.ixb or legacy .json).\n" ++
  "  show BASE LABEL [--top N]               Inspect one case's largest circuits and functions.\n" ++
  "  --self-test                             Run codec, FFT-cost, extract/diff/show checks.\n" ++
  "  --help                                  Show this message."

/-- Per-circuit row count, cache hits, and rounded FFT cost (indexed into
`Baseline.circuits`). -/
structure CircuitCost where
  circuitIdx : Nat
  rows : Nat
  cacheHits : Nat
  cost : Nat
  deriving BEq, Repr, Inhabited

/-- Per-function memo row count and cache hits from `*.stats.json.functions.json`. -/
structure FnCost where
  name : String
  rows : Nat
  cacheHits : Nat
  deriving BEq, Repr, Inhabited

/-- Cost summary for one labelled benchmark or pinned claim case. -/
structure CaseCost where
  label : String
  fft : Option Nat
  fftModel : Option Nat
  rows : Option Nat
  circuits : Array CircuitCost
  file : Option String
  functions : Option (Array FnCost)
  deriving BEq, Repr, Inhabited

/-- Complete extracted baseline across all cases and interned circuit names. -/
structure Baseline where
  circuits : Array String
  cases : Array CaseCost
  deriving BEq, Repr, Inhabited

def CaseCost.total? (c : CaseCost) : Option Nat :=
  match c.fft with
  | some v => some v
  | none => c.fftModel

/-! ## Binary codec (`IXBL` v1) -/

private def magic : ByteArray :=
  ByteArray.mk #[0x49, 0x58, 0x42, 0x4C, 0x01] -- "IXBL" + version 1

private def putVarNat (buf : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := buf
  let mut v := n
  repeat
    let lo : UInt8 := UInt8.ofNat (v &&& 0x7f)
    v := v >>> 7
    if v == 0 then
      out := out.push lo
      break
    else
      out := out.push (lo ||| 0x80)
  return out

private def putStr (buf : ByteArray) (s : String) : ByteArray :=
  let bytes := s.toUTF8
  (putVarNat buf bytes.size).append bytes

private def putOpt {α : Type} (put : ByteArray → α → ByteArray) (buf : ByteArray) :
    Option α → ByteArray
  | none => buf.push 0
  | some v => put (buf.push 1) v

private def putArr {α : Type} (put : ByteArray → α → ByteArray) (buf : ByteArray)
    (xs : Array α) : ByteArray :=
  xs.foldl put (putVarNat buf xs.size)

private def putCircuitCost (buf : ByteArray) (c : CircuitCost) : ByteArray :=
  let buf := putVarNat buf c.circuitIdx
  let buf := putVarNat buf c.rows
  let buf := putVarNat buf c.cacheHits
  putVarNat buf c.cost

private def putFnCost (buf : ByteArray) (f : FnCost) : ByteArray :=
  let buf := putStr buf f.name
  let buf := putVarNat buf f.rows
  putVarNat buf f.cacheHits

private def putCaseCost (buf : ByteArray) (c : CaseCost) : ByteArray :=
  let buf := putStr buf c.label
  let buf := putOpt putVarNat buf c.fft
  let buf := putOpt putVarNat buf c.fftModel
  let buf := putOpt putVarNat buf c.rows
  let buf := putArr putCircuitCost buf c.circuits
  let buf := putOpt putStr buf c.file
  putOpt (putArr putFnCost) buf c.functions

/-- Encode a `Baseline` into the compact typed binary format (`IXBL` v1). -/
def encodeBinary (b : Baseline) : ByteArray :=
  let buf := putArr putStr magic b.circuits
  putArr putCaseCost buf b.cases

private abbrev DecodeM := StateT Nat (Except String)

private def getByte (bytes : ByteArray) : DecodeM UInt8 := do
  let pos ← get
  if pos < bytes.size then
    set (pos + 1)
    return bytes.get! pos
  else
    throw s!"unexpected EOF at byte {pos}"

private def getVarNat (bytes : ByteArray) : DecodeM Nat := do
  let mut result : Nat := 0
  let mut shift : Nat := 0
  for _ in [:20] do
    let b ← getByte bytes
    result := result ||| ((b.toNat &&& 0x7f) <<< shift)
    if (b &&& 0x80) == 0 then
      return result
    shift := shift + 7
  throw "varint exceeds maximum length"

private def getStr (bytes : ByteArray) : DecodeM String := do
  let len ← getVarNat bytes
  let pos ← get
  if pos + len > bytes.size then
    throw s!"string length {len} exceeds remaining bytes at offset {pos}"
  set (pos + len)
  match String.fromUTF8? (bytes.extract pos (pos + len)) with
  | some s => return s
  | none => throw s!"invalid UTF-8 string at offset {pos}"

private def getOpt {α : Type} (bytes : ByteArray) (dec : DecodeM α) : DecodeM (Option α) := do
  match ← getByte bytes with
  | 0 => return none
  | 1 => return some (← dec)
  | tag => throw s!"invalid Option tag {tag}"

private def getArr {α : Type} (bytes : ByteArray) (dec : DecodeM α) : DecodeM (Array α) := do
  let len ← getVarNat bytes
  let mut out := Array.mkEmpty len
  for _ in [:len] do
    out := out.push (← dec)
  return out

private def getCircuitCost (bytes : ByteArray) : DecodeM CircuitCost := do
  let circuitIdx ← getVarNat bytes
  let rows ← getVarNat bytes
  let cacheHits ← getVarNat bytes
  let cost ← getVarNat bytes
  return { circuitIdx, rows, cacheHits, cost }

private def getFnCost (bytes : ByteArray) : DecodeM FnCost := do
  let name ← getStr bytes
  let rows ← getVarNat bytes
  let cacheHits ← getVarNat bytes
  return { name, rows, cacheHits }

private def getCaseCost (bytes : ByteArray) : DecodeM CaseCost := do
  let label ← getStr bytes
  let fft ← getOpt bytes (getVarNat bytes)
  let fftModel ← getOpt bytes (getVarNat bytes)
  let rows ← getOpt bytes (getVarNat bytes)
  let circuits ← getArr bytes (getCircuitCost bytes)
  let file ← getOpt bytes (getStr bytes)
  let functions ← getOpt bytes (getArr bytes (getFnCost bytes))
  return { label, fft, fftModel, rows, circuits, file, functions }

/-- Decode a `Baseline` from the `IXBL` v1 binary format. -/
def decodeBinary (bytes : ByteArray) : Except String Baseline := do
  if bytes.size < magic.size then
    throw "baseline file too short"
  for i in [:magic.size] do
    if bytes.get! i != magic.get! i then
      throw "invalid IXBL baseline magic/version header"
  let dec : DecodeM Baseline := do
    let circuits ← getArr bytes (getStr bytes)
    let cases ← getArr bytes (getCaseCost bytes)
    return { circuits, cases }
  let (baseline, endPos) ← dec.run magic.size
  if endPos != bytes.size then
    throw s!"trailing bytes in baseline: read {endPos} of {bytes.size}"
  return baseline

private def optNatFromJson (j : Json) (key : String) : Except String (Option Nat) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => v.getNat?.map some

private def optStrFromJson (j : Json) (key : String) : Except String (Option String) :=
  match j.getObjVal? key with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => v.getStr?.map some

/-- Legacy JSON baseline decoder so historical `.json` baselines can still be
compared with `diff` or inspected with `show`. -/
def decodeLegacyJson (text : String) : Except String Baseline := do
  let root ← Json.parse text
  let circuits ← root.getObjValAs? (Array String) "circuits"
  let casesObj ← (← root.getObjVal? "cases").getObj?
  let mut cases : Array CaseCost := #[]
  for (label, cJson) in casesObj.toList do
    let fft ← optNatFromJson cJson "fft"
    let fftModel ← optNatFromJson cJson "fft_model"
    let rows ← optNatFromJson cJson "rows"
    let file ← optStrFromJson cJson "file"
    let circObj ← (← cJson.getObjVal? "circuits").getObj?
    let mut circCosts : Array CircuitCost := #[]
    for (idxStr, valsJson) in circObj.toList do
      let some idx := idxStr.toNat? | throw s!"invalid circuit index {idxStr}"
      let vals ← valsJson.getArr?
      unless vals.size == 3 do throw s!"expected 3-element circuit tuple for {label}"
      circCosts := circCosts.push {
        circuitIdx := idx
        rows := ← vals[0]!.getNat?
        cacheHits := ← vals[1]!.getNat?
        cost := ← vals[2]!.getNat?
      }
    let functions ← match cJson.getObjVal? "functions" with
      | .error _ | .ok .null => pure none
      | .ok fJson => do
        let fObj ← fJson.getObj?
        let mut fns : Array FnCost := #[]
        for (fname, fvalsJson) in fObj.toList do
          let fvals ← fvalsJson.getArr?
          unless fvals.size == 2 do throw s!"expected 2-element function tuple for {label}:{fname}"
          fns := fns.push {
            name := fname
            rows := ← fvals[0]!.getNat?
            cacheHits := ← fvals[1]!.getNat?
          }
        pure (some fns)
    cases := cases.push { label, fft, fftModel, rows, circuits := circCosts, file, functions }
  return { circuits, cases := cases.qsort (·.label < ·.label) }

/-- Load a baseline from either the native `.ixb` binary format or a legacy
`.json` baseline snapshot. -/
def loadBaseline (path : FilePath) : IO Baseline := do
  let bytes ← IO.FS.readBinFile path
  if bytes.size >= 4 &&
      bytes.get! 0 == 0x49 && bytes.get! 1 == 0x58 &&
      bytes.get! 2 == 0x42 && bytes.get! 3 == 0x4C then
    IO.ofExcept (decodeBinary bytes)
  else
    let text ← match String.fromUTF8? bytes with
      | some s => pure s
      | none => throw <| IO.userError s!"{path}: unrecognized binary format (expected IXBL header)"
    IO.ofExcept (decodeLegacyJson text)

/-! ## Log parsing and sidecar extraction -/

private def hasSubstr (text pattern : String) : Bool :=
  (text.splitOn pattern).length > 1

/-- Parse a harness FFT line `FFT <label>: <cost> (expected <...>)`. -/
def parseFftLine (raw : String) : Option (String × Nat) := do
  let line := raw.trimAsciiEnd.toString
  guard (line.startsWith "FFT " && line.endsWith ")")
  let body := (line.drop 4).toString
  let expParts := body.splitOn " (expected "
  guard (expParts.length >= 2)
  let expTail := expParts.getLast!
  -- `expTail` must end with `)` and have no earlier `)` (matching `[^)]*`).
  let expInner := (expTail.dropEnd 1).toString
  guard (!expInner.contains ')')
  let prefixPart := " (expected ".intercalate expParts.dropLast
  let colonParts := prefixPart.splitOn ": "
  guard (colonParts.length >= 2)
  let numStr := colonParts.getLast!
  guard (!numStr.isEmpty && numStr.toList.all Char.isDigit)
  let cost ← numStr.toNat?
  let label := ": ".intercalate colonParts.dropLast
  return (label, cost)

private def relPath (path base : FilePath) : String :=
  let p := path.normalize.toString
  let b := base.normalize.toString
  let pref := if b.endsWith "/" then b else b ++ "/"
  if p.startsWith pref then (p.drop pref.length).toString else p

private def readFileLossy (path : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile path
  match String.fromUTF8? bytes with
  | some s => return s
  | none =>
    let mut chars : Array Char := Array.mkEmpty bytes.size
    for i in [:bytes.size] do
      let b := bytes.get! i
      chars := chars.push (if b < 128 then Char.ofNat b.toNat else '?')
    return String.ofList chars.toList

/-- Extract a `Baseline` from all `*.stats.json` (and companion
`*.stats.json.functions.json`) sidecars under `outdir` and `FFT ...` totals in
`logs`. Returns the baseline plus any warning/summary lines for stderr. -/
def extractBaseline (outdir : FilePath) (logs : Array FilePath) :
    IO (Baseline × Array String) := do
  let mut totals : Std.HashMap String Nat := {}
  for log in logs do
    let text ← readFileLossy log
    for line in text.splitOn "\n" do
      if let some (label, cost) := parseFftLine line then
        totals := totals.insert label cost

  let mut statsFiles : Array FilePath := #[]
  if ← outdir.isDir then
    for path in ← outdir.walkDir do
      if !(← path.isDir) && (path.fileName.getD "").endsWith ".stats.json" then
        statsFiles := statsFiles.push path
  statsFiles := statsFiles.qsort (·.toString < ·.toString)

  let mut names : Array String := #[]
  let mut nameIndex : Std.HashMap String Nat := {}
  let mut caseMap : Std.HashMap String CaseCost := {}

  for path in statsFiles do
    let rawJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
    let dataObj ← IO.ofExcept rawJson.getObj?
    let fpath : FilePath := path.toString ++ ".functions.json"
    let mut fdata : Std.HashMap String (Array FnCost) := {}
    if ← fpath.pathExists then
      let fJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile fpath)
      let fObj ← IO.ofExcept fJson.getObj?
      for (label, entriesJson) in fObj.toList do
        let arr ← IO.ofExcept entriesJson.getArr?
        let fns ← IO.ofExcept <| arr.mapM fun e => do
          let name ← e.getObjValAs? String "name"
          let rows ← e.getObjValAs? Nat "rows"
          let cacheHits ← e.getObjValAs? Nat "cache_hits"
          return { name, rows, cacheHits : FnCost }
        fdata := fdata.insert label fns

    for (label, mJson) in dataObj.toList do
      let meas ← IO.ofExcept <| Aiur.ExecutionMeasurements.fromJson mJson
      let stats := Aiur.computeStats meas
      let fftModel := stats.roundedFftCost
      let mut circCosts : Array CircuitCost := #[]
      let mut totalRows : Nat := 0
      for c in meas.circuits do
        let cost := Aiur.fftCost c.shape c.height meas.logBlowup
        if c.height == 0 then continue
        let idx ← match nameIndex[c.name]? with
          | some i => pure i
          | none =>
            let i := names.size
            names := names.push c.name
            nameIndex := nameIndex.insert c.name i
            pure i
        circCosts := circCosts.push {
          circuitIdx := idx
          rows := c.height
          cacheHits := c.cacheHits
          cost := cost.round.toUInt64.toNat
        }
        totalRows := totalRows + c.height
      if caseMap.contains label then
        throw <| IO.userError s!"label twice: {label}"
      let c : CaseCost := {
        label
        fft := totals[label]?
        fftModel := some fftModel
        rows := some totalRows
        circuits := circCosts
        file := some (relPath path outdir)
        functions := fdata[label]?
      }
      caseMap := caseMap.insert label c

  for (label, total) in totals.toList do
    unless caseMap.contains label do
      caseMap := caseMap.insert label {
        label
        fft := some total
        fftModel := none
        rows := none
        circuits := #[]
        file := none
        functions := none
      }

  let cases := (caseMap.toArray.map (·.2)).qsort (·.label < ·.label)
  let mut stderrLines : Array String := #[]
  let mut badCount : Nat := 0
  for c in cases do
    if let (some logged, some model) := (c.fft, c.fftModel) then
      let delta := Int.natAbs ((logged : Int) - (model : Int))
      if delta > 1 then
        badCount := badCount + 1
        stderrLines := stderrLines.push
          s!"warning: {c.label}: logged {logged} but sidecar gives {model}"
  stderrLines := stderrLines.push
    s!"extracted {cases.size} cases, {totals.size} logged totals, {names.size} circuits, {badCount} disagreements"
  return ({ circuits := names, cases }, stderrLines)

/-! ## Formatting, `diff`, and `show` -/

private def padLeft (s : String) (w : Nat) : String :=
  if s.length >= w then s
  else String.ofList (List.replicate (w - s.length) ' ') ++ s

private def padRight (s : String) (w : Nat) : String :=
  if s.length >= w then s
  else s ++ String.ofList (List.replicate (w - s.length) ' ')

private def padZero (n digits : Nat) : String :=
  let s := toString n
  if s.length >= digits then s
  else String.ofList (List.replicate (digits - s.length) '0') ++ s

private def formatSci4 (n : Nat) : String :=
  if n == 0 then "0.0000e+00"
  else
    let f := n.toFloat
    let e := f.log10.floor
    let scaled := (f / (10.0 ^ e) * 10000.0).round
    let (scaled, e) := if scaled >= 100000.0 then (10000.0, e + 1.0) else (scaled, e)
    let k := scaled.toUInt64.toNat
    let exp := e.toUInt64.toNat
    s!"{k / 10000}.{padZero (k % 10000) 4}e+{padZero exp 2}"

private def formatRatio4 (a b : Nat) : String :=
  if a == 0 then "xnan"
  else
    let r := b.toFloat / a.toFloat
    let scaled := (r * 10000.0).round.toUInt64.toNat
    s!"x{scaled / 10000}.{padZero (scaled % 10000) 4}"

private def formatSigned (d : Int) (width : Nat) : String :=
  let s := if d >= 0 then s!"+{d}" else toString d
  padLeft s width

private def formatOptNat (x : Option Nat) : String :=
  match x with
  | some n => toString n
  | none => "None"

private def short (name : String) (n : Nat := 90) : String :=
  if name.length <= n then name
  else (name.take (n - 3)).toString ++ "..."

def suiteOf (label : String) : String :=
  let prefixes := [
    "eval ", "check ", "binding ", "shard ", "corpus ",
    "ind-decl decl ", "ind-decl decl-ind ", "ind-decl decl-rec ", "ind-decl check ", "ind-decl std ", "ind-decl model "
  ]
  match prefixes.find? (label.startsWith ·) with
  | some p => p.trimAscii.toString
  | none => "other"

private def circuitsByName (base : Baseline) (c : CaseCost) :
    Std.HashMap String (Nat × Nat × Nat) :=
  c.circuits.foldl (init := {}) fun m cc =>
    let name := base.circuits[cc.circuitIdx]?.getD s!"<circuit#{cc.circuitIdx}>"
    m.insert name (cc.rows, cc.cacheHits, cc.cost)

private def fnsByName (c : CaseCost) : Option (Std.HashMap String (Nat × Nat)) :=
  c.functions.map fun fns =>
    fns.foldl (init := {}) fun m f => m.insert f.name (f.rows, f.cacheHits)

private def caseMapOf (base : Baseline) : Std.HashMap String CaseCost :=
  base.cases.foldl (init := {}) fun m c => m.insert c.label c

/-- Produce the `diff` report text comparing two baselines. -/
def renderDiff (old new : Baseline) (top : Nat) : String := Id.run do
  let oc := caseMapOf old
  let nc := caseMapOf new
  let mut common : Array String := #[]
  let mut onlyOld : Array String := #[]
  let mut onlyNew : Array String := #[]
  for c in old.cases do
    if nc.contains c.label then common := common.push c.label
    else onlyOld := onlyOld.push c.label
  for c in new.cases do
    unless oc.contains c.label do onlyNew := onlyNew.push c.label
  common := common.qsort (· < ·)
  onlyOld := onlyOld.qsort (· < ·)
  onlyNew := onlyNew.qsort (· < ·)

  let mut moved : Array (String × Option Nat × Option Nat) := #[]
  for l in common do
    let a := oc[l]!.total?
    let b := nc[l]!.total?
    if a != b then
      moved := moved.push (l, a, b)

  let absDelta (t : String × Option Nat × Option Nat) : Nat :=
    Int.natAbs (((t.2.2.getD 0) : Int) - ((t.2.1.getD 0) : Int))
  let movedSorted := moved.qsort fun x y =>
    let dx := absDelta x
    let dy := absDelta y
    if dx != dy then dx > dy else x.1 < y.1

  let mut lines : Array String := #[
    s!"cases: {common.size} in both, {moved.size} moved, {onlyOld.size} only in old, {onlyNew.size} only in new"
  ]

  let mut sums : Std.HashMap String (Nat × Nat × Nat) := {}
  for l in common do
    let k := suiteOf l
    let (sa, sb, sn) := sums[k]?.getD (0, 0, 0)
    sums := sums.insert k (sa + oc[l]!.total?.getD 0, sb + nc[l]!.total?.getD 0, sn + 1)
  lines := lines.push ""
  lines := lines.push "sums by suite (old -> new, ratio):"
  for (k, (a, b, n)) in sums.toArray.qsort (·.1 < ·.1) do
    lines := lines.push
      s!"  {padRight k 10} {padLeft (toString n) 4} cases  {formatSci4 a} -> {formatSci4 b}  {formatRatio4 a b}"

  if !movedSorted.isEmpty then
    lines := lines.push ""
    lines := lines.push "moved cases (largest absolute change first):"
    for (l, a?, b?) in movedSorted do
      let aStr := padLeft (formatOptNat a?) 16
      let bStr := padLeft (formatOptNat b?) 16
      let ratio := formatRatio4 (a?.getD 0) (b?.getD 0)
      lines := lines.push s!"  {aStr} -> {bStr}  {ratio}  {l}"

  for l in onlyOld do
    lines := lines.push s!"  only in old: {l} ({formatOptNat oc[l]!.total?})"
  for l in onlyNew do
    lines := lines.push s!"  only in new: {l} ({formatOptNat nc[l]!.total?})"

  for (l, a?, b?) in movedSorted.extract 0 (min top movedSorted.size) do
    lines := lines.push ""
    lines := lines.push s!"== {l}: {formatOptNat a?} -> {formatOptNat b?}"
    let co := circuitsByName old oc[l]!
    let cn := circuitsByName new nc[l]!
    let mut allNames : Std.HashMap String Unit := {}
    for (name, _) in co.toList do allNames := allNames.insert name ()
    for (name, _) in cn.toList do allNames := allNames.insert name ()
    let mut rows : Array (Int × Int × Nat × Nat × String) := #[]
    for (name, _) in allNames.toList do
      let (ro, _, ko) := co[name]?.getD (0, 0, 0)
      let (rn, _, kn) := cn[name]?.getD (0, 0, 0)
      if ro != rn || ko != kn then
        rows := rows.push ((kn : Int) - (ko : Int), (rn : Int) - (ro : Int), ro, rn, name)
    let rowsSorted := rows.qsort fun x y =>
      if Int.natAbs x.1 != Int.natAbs y.1 then Int.natAbs x.1 > Int.natAbs y.1
      else x.2.2.2.2 < y.2.2.2.2
    for (dk, _, ro, rn, name) in rowsSorted.extract 0 (min top rowsSorted.size) do
      lines := lines.push
        s!"   cost {formatSigned dk 14}  rows {padLeft (toString ro) 11} -> {padLeft (toString rn) 11}  {short name}"
    if let (some fo, some fn) := (fnsByName oc[l]!, fnsByName nc[l]!) then
      if !fo.isEmpty || !fn.isEmpty then
        let mut fNames : Std.HashMap String Unit := {}
        for (name, _) in fo.toList do fNames := fNames.insert name ()
        for (name, _) in fn.toList do fNames := fNames.insert name ()
        let mut frows : Array (Int × Nat × Nat × String) := #[]
        for (name, _) in fNames.toList do
          let a1 := (fo[name]?.getD (0, 0)).1
          let b1 := (fn[name]?.getD (0, 0)).1
          if a1 != b1 then
            frows := frows.push ((b1 : Int) - (a1 : Int), a1, b1, name)
        let frowsSorted := frows.qsort fun x y =>
          if Int.natAbs x.1 != Int.natAbs y.1 then Int.natAbs x.1 > Int.natAbs y.1
          else x.2.2.2 < y.2.2.2
        for (d, a1, b1, name) in frowsSorted.extract 0 (min top frowsSorted.size) do
          lines := lines.push
            s!"   fn rows {formatSigned d 12}  {padLeft (toString a1) 11} -> {padLeft (toString b1) 11}  {short name}"

  return "\n".intercalate lines.toList

/-- Produce the `show` report text for one case label. -/
def renderShow (base : Baseline) (label : String) (top : Nat) : Except String String := do
  let cmap := caseMapOf base
  let some c := cmap[label]? | throw s!"case label not found: {label}"
  let mut lines : Array String := #[
    s!"{label}: fft {formatOptNat c.total?}, rows {formatOptNat c.rows}"
  ]
  let circs := (circuitsByName base c).toArray.qsort fun x y =>
    if x.2.2.2 != y.2.2.2 then x.2.2.2 > y.2.2.2 else x.1 < y.1
  for (name, (r, h, k)) in circs.extract 0 (min top circs.size) do
    lines := lines.push
      s!"  {padLeft (toString k) 16}  rows {padLeft (toString r) 11}  hits {padLeft (toString h) 11}  {short name}"
  if let some fns := c.functions then
    if !fns.isEmpty then
      lines := lines.push "  functions by rows:"
      let fnsSorted := fns.qsort fun x y =>
        if x.rows != y.rows then x.rows > y.rows else x.name < y.name
      for f in fnsSorted.extract 0 (min top fnsSorted.size) do
        lines := lines.push
          s!"  rows {padLeft (toString f.rows) 11}  hits {padLeft (toString f.cacheHits) 11}  {short f.name}"
  return "\n".intercalate lines.toList

/-! ## `run` subcommand (ports `tools/ixvm/baseline/run.sh`) -/

private def runLogged (cmd : String) (args : Array String)
    (env : Array (String × Option String)) (log : FilePath) : IO UInt32 := do
  let child ← IO.Process.spawn {
    cmd := "sh"
    args := #["-c", "log=$1; shift; exec \"$@\" >\"$log\" 2>&1", "sh", log.toString, cmd] ++ args
    env
  }
  child.wait

private def countPrefixedLines (path : FilePath) (pref : String) : IO Nat := do
  let text ← IO.FS.readFile path
  let mut n := 0
  for line in text.splitOn "\n" do
    if line.startsWith pref then n := n + 1
  return n

private def checkedStdout (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"{cmd} failed (exit {out.exitCode}): {out.stderr}"
  return out.stdout.trimAscii.toString

/-- Summarize `ix check --report` JSON for `CORPUS=1` into `FFT corpus ...` lines. -/
def formatCorpusReport (reportJsonText : String) : Except String String := do
  let r ← Json.parse reportJsonText
  let leaves ← (← r.getObjVal? "leaves").getArr?
  let mut lines : Array String := #[]
  let mut tot : Nat := 0
  for leaf in leaves do
    let shard ← leaf.getObjValAs? Nat "shard"
    let parts ← (← leaf.getObjVal? "parts").getArr?
    for (p, i) in parts.zipIdx do
      let blocks := match p.getObjVal? "blocks" >>= (·.getArr?) with
        | .ok bs => bs.size
        | .error _ => 0
      let refused := match p.getObjVal? "status" with
        | .ok .null => false
        | .ok (.str s) => !s.isEmpty
        | .ok (.bool b) => b
        | .ok _ => true
        | .error _ => false
      if refused then
        lines := lines.push s!"corpus initstd shard {shard}.{i} ({blocks} blocks) refused"
      else
        let c := match p.getObjVal? "report" >>= (·.getObjValAs? Nat "fft-cost") with
          | .ok v => v
          | .error _ => 0
        tot := tot + c
        lines := lines.push
          s!"FFT corpus initstd shard {shard}.{i} ({blocks} blocks): {c} (expected none)"
  lines := lines.push s!"FFT corpus initstd total: {tot} (expected none)"
  return "\n".intercalate lines.toList ++ "\n"

def runSuite (outDir : FilePath) (recorded? : Option FilePath) : IO UInt32 := do
  IO.FS.createDirAll outDir
  let out ← IO.FS.realPath outDir
  let runTxt := out / "run.txt"
  IO.FS.writeFile runTxt ""
  let log (msg : String) : IO Unit := do
    let line := s!"[baseline] {msg}"
    IO.println line
    (← IO.getStdout).flush
    let prev ← IO.FS.readFile runTxt
    IO.FS.writeFile runTxt (prev ++ line ++ "\n")

  let commit ← checkedStdout "git" #["rev-parse", "HEAD"]
  let utc ← checkedStdout "date" #["-u", "+%FT%TZ"]
  log s!"commit {commit} {utc}"

  if (← runLogged "lake" #["build", "--wfail", "IxTests", "ixvm/ixvm"] #[] (out / "build.log")) != 0 then
    log "build failed"
    return 1
  if (← runLogged "cargo" #["build", "--release", "--locked", "-p", "ixvm", "--bin", "ixvm-proof",
      "--features", "parallel"] #[] (out / "host.log")) != 0 then
    log "host build failed"
    return 1
  discard <| checkedStdout "cp" #["-p", "target/release/ixvm-proof", (out / "ixvm-proof").toString]
  if (← runLogged "lake" #["env", "IxVM/.lake/build/bin/ixvm", "export-claim-trace",
      (out / "ixvm.ixa").toString] #[] (out / "export.log")) != 0 then
    log "export failed"
    return 1
  let shaOut ← checkedStdout "sha256sum" #["--", (out / "ixvm.ixa").toString]
  let sha16 := ((shaOut.splitOn " ").headD "").take 16 |>.toString
  log s!"artifact sha256 {sha16}"

  let runEnv : Array (String × Option String) := #[
    ("IX_AIUR_HOST", some (out / "ixvm-proof").toString),
    ("IX_AIUR_ARTIFACT", some (out / "ixvm.ixa").toString),
    ("IX_TEST_OUTPUT_DIR", some (out / "out").toString),
    ("IXVM_FUNCTION_STATS", some "1")
  ]

  let t0 ← IO.monoMsNow
  let rcPins ← runLogged "lake" #["test", "--wfail", "--", "ixvm-kernel-checks", "ixvm-eval"]
    runEnv (out / "pins.log")
  let secsPins := ((← IO.monoMsNow) - t0) / 1000
  let fftPins ← countPrefixedLines (out / "pins.log") "FFT "
  let failPins ← countPrefixedLines (out / "pins.log") "FAILED"
  log s!"pinned suites rc={rcPins} {secsPins}s; {fftPins} FFT lines, {failPins} FAILED lines"
  let mut logs : Array FilePath := #[out / "pins.log"]

  let benchEnabled := (← IO.getEnv "BENCH").getD "1" == "1"
  let hasIndDeclBench ← do
    if ← (FilePath.mk "Tests/Main.lean").pathExists then
      pure (hasSubstr (← IO.FS.readFile "Tests/Main.lean") "\"ixvm-ind-decl-bench\"")
    else pure false
  if benchEnabled && hasIndDeclBench then
    let t1 ← IO.monoMsNow
    let rcBench ← runLogged "lake" #["test", "--wfail", "--", "ixvm-ind-decl-bench"]
      runEnv (out / "bench.log")
    let secsBench := ((← IO.monoMsNow) - t1) / 1000
    let fftBench ← countPrefixedLines (out / "bench.log") "FFT "
    log s!"bench rc={rcBench} {secsBench}s; {fftBench} FFT lines"
    logs := logs.push (out / "bench.log")

  if (← IO.getEnv "CORPUS").getD "0" == "1" then
    let t2 ← IO.monoMsNow
    let cwd ← IO.currentDir
    let ixBin := (cwd / ".lake" / "build" / "bin" / "ix").toString
    discard <| runLogged "lake" #["build", "--wfail", "ix"] runEnv (out / "corpus-build.log")
    discard <| runLogged "lake" #[
      "env", ixBin, "compile-lean", "Benchmarks/Compile/CompileInitStd.lean",
      "--no-build", "--out", (out / "initstd.ixe").toString
    ] runEnv (out / "corpus-compile.log")
    discard <| runLogged "lake" #[
      "env", ixBin, "shard", (out / "initstd.ixe").toString,
      "--shards", "24", "--out", (out / "initstd.ixes").toString
    ] runEnv (out / "corpus-shard.log")
    discard <| runLogged "lake" #[
      "env", ixBin, "check", "--ixe", (out / "initstd.ixe").toString,
      "--ixes", (out / "initstd.ixes").toString,
      "--aiur-artifact", (out / "ixvm.ixa").toString,
      "--assume-binding", "--jobs", "3", "--keep-going",
      "--report", (out / "initstd.report.json").toString
    ] runEnv (out / "corpus-check.log")
    let corpusRc ← try
      let summary ← IO.ofExcept <| formatCorpusReport (← IO.FS.readFile (out / "initstd.report.json"))
      IO.FS.writeFile (out / "corpus.log") summary
      pure (0 : UInt32)
    catch e =>
      IO.FS.writeFile (out / "corpus.log") s!"corpus report error: {e}\n"
      pure (1 : UInt32)
    let secsCorpus := ((← IO.monoMsNow) - t2) / 1000
    let lastCorpus := ((← IO.FS.readFile (out / "corpus.log")).trimAsciiEnd.toString.splitOn "\n").getLastD ""
    log s!"corpus rc={corpusRc} {secsCorpus}s; {lastCorpus}"
    logs := logs.push (out / "corpus.log")

  let (baseline, extractMsgs) ← extractBaseline (out / "out") logs
  IO.FS.writeBinFile (out / "baseline.ixb") (encodeBinary baseline)
  IO.FS.writeFile (out / "extract.txt") ("\n".intercalate extractMsgs.toList ++ "\n")
  log (extractMsgs.back?.getD "")

  if let some recPath := recorded? then
    let old ← loadBaseline recPath
    let diffText := renderDiff old baseline 15
    IO.FS.writeFile (out / "diff.txt") (diffText ++ "\n")
    let firstLine := (diffText.splitOn "\n").headD ""
    log firstLine
  return 0

/-! ## CLI parsing and self-test -/

inductive Command where
  | help
  | selfTest
  | run (out : FilePath) (recorded? : Option FilePath)
  | extract (outdir : FilePath) (logs : Array FilePath) (outFile? : Option FilePath)
  | diff (oldPath newPath : FilePath) (top : Nat)
  | showCase (basePath : FilePath) (label : String) (top : Nat)
  deriving BEq, Repr

private def parseTop (rest : List String) (defaultTop : Nat) : Except String Nat :=
  match rest with
  | [] => .ok defaultTop
  | ["--top", nStr] =>
    match nStr.toNat? with
    | some n => .ok n
    | none => .error s!"invalid --top value: {nStr}"
  | other => .error s!"unexpected trailing arguments: {" ".intercalate other}"

private def parseExtractRest : List String → Array FilePath → Option FilePath →
    Except String (Array FilePath × Option FilePath)
  | [], logs, outFile? => .ok (logs, outFile?)
  | "--out" :: p :: rest, logs, _ => parseExtractRest rest logs (some p)
  | ["--out"], _, _ => .error "--out expects a file path"
  | p :: rest, logs, outFile? => parseExtractRest rest (logs.push p) outFile?

def parseArgs : List String → Except String Command
  | ["--help"] | ["-h"] => .ok .help
  | ["--self-test"] => .ok .selfTest
  | ["run", out] => .ok (.run out none)
  | ["run", out, recPath] => .ok (.run out (some recPath))
  | "extract" :: outdir :: rest => do
    let (logs, outFile?) ← parseExtractRest rest #[] none
    .ok (.extract outdir logs outFile?)
  | "diff" :: oldPath :: newPath :: rest => do
    let top ← parseTop rest 15
    .ok (.diff oldPath newPath top)
  | "show" :: basePath :: label :: rest => do
    let top ← parseTop rest 25
    .ok (.showCase basePath label top)
  | _ => .error "invalid arguments"

private def ensure (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

partial def freshTmpDir : IO FilePath := do
  let stamp := (← IO.monoNanosNow) + 7919 * (← IO.Process.getPID).toNat
  let hex := String.ofList ((Nat.toDigits 16 (stamp % 16 ^ 8 + 16 ^ 8)).drop 1)
  let dir : FilePath := s!"/tmp/ixvm-baseline-test-{hex}"
  try IO.FS.createDir dir; return dir
  catch _ => freshTmpDir

def selfTest : IO Unit := do
  -- 1. FFT line parsing
  ensure (parseFftLine "FFT check Nat.add_comm: 12345 (expected 12345)" ==
    some ("check Nat.add_comm", 12345)) "parse basic FFT line"
  ensure (parseFftLine "FFT eval a: b: 999 (expected none)   " ==
    some ("eval a: b", 999)) "parse FFT line with colon in label and trailing spaces"
  ensure (parseFftLine "not an fft line" == none) "ignore non-FFT line"

  -- 2. Binary codec round-trip
  let sample : Baseline := {
    circuits := #["circuit_a", "circuit_b"]
    cases := #[
      { label := "check Nat.add_comm", fft := some 565, fftModel := some 565, rows := some 5,
        circuits := #[{ circuitIdx := 0, rows := 1, cacheHits := 3, cost := 61 },
                      { circuitIdx := 1, rows := 4, cacheHits := 0, cost := 504 }],
        file := some "pins.stats.json",
        functions := some #[{ name := "IxVM::verify", rows := 4, cacheHits := 2 }] },
      { label := "corpus initstd total", fft := some 1000, fftModel := none, rows := none,
        circuits := #[], file := none, functions := none }
    ]
  }
  let encoded := encodeBinary sample
  let decoded ← IO.ofExcept (decodeBinary encoded)
  ensure (decoded == sample) "binary codec round-trip"

  -- 3. End-to-end extract (using Aiur.computeStats.roundedFftCost), diff, show
  let tmp ← freshTmpDir
  try
    let statsJson := Json.mkObj [
      ("check Nat.add_comm", Json.mkObj [
        ("log_blowup", toJson (2 : Nat)),
        ("extension_degree", toJson (2 : Nat)),
        ("circuits", Json.arr #[
          Json.mkObj [
            ("name", toJson "small"), ("stage1_width", toJson (3 : Nat)),
            ("stage2_width", toJson (2 : Nat)), ("quotient_degree", toJson (2 : Nat)),
            ("preprocessed_width", toJson (100 : Nat)), ("preprocessed_height", toJson (0 : Nat)),
            ("rows", toJson (1 : Nat)), ("cache_hits", toJson (3 : Nat))
          ],
          Json.mkObj [
            ("name", toJson "large"), ("stage1_width", toJson (3 : Nat)),
            ("stage2_width", toJson (2 : Nat)), ("quotient_degree", toJson (2 : Nat)),
            ("preprocessed_width", toJson (100 : Nat)), ("preprocessed_height", toJson (0 : Nat)),
            ("rows", toJson (4 : Nat)), ("cache_hits", toJson (0 : Nat))
          ]
        ])
      ])
    ]
    let fnsJson := Json.mkObj [
      ("check Nat.add_comm", Json.arr #[
        Json.mkObj [("name", toJson "IxVM::eval"), ("rows", toJson (4 : Nat)),
                    ("cache_hits", toJson (1 : Nat))]
      ])
    ]
    IO.FS.writeFile (tmp / "case.stats.json") statsJson.pretty
    IO.FS.writeFile (tmp / "case.stats.json.functions.json") fnsJson.pretty
    IO.FS.writeFile (tmp / "pins.log")
      "FFT check Nat.add_comm: 565 (expected 565)\nFFT eval extra: 42 (expected none)\n"

    let (extracted, msgs) ← extractBaseline tmp #[tmp / "pins.log"]
    ensure (extracted.cases.size == 2) s!"extracted case count: {extracted.cases.size}"
    ensure (msgs.back?.getD "" == "extracted 2 cases, 2 logged totals, 2 circuits, 0 disagreements")
      s!"unexpected extract summary: {msgs.back?.getD ""}"
    let bPath := tmp / "base.ixb"
    IO.FS.writeBinFile bPath (encodeBinary extracted)
    let loaded ← loadBaseline bPath
    ensure (loaded == extracted) "loadBaseline .ixb round-trip"

    let shown ← IO.ofExcept (renderShow loaded "check Nat.add_comm" 10)
    ensure (hasSubstr shown "check Nat.add_comm: fft 565, rows 5") "show header"
    ensure (hasSubstr shown "IxVM::eval") "show functions"

    let bumped := { loaded with
      cases := loaded.cases.map fun c =>
        if c.label == "check Nat.add_comm" then { c with fft := some 600 } else c
    }
    let diffText := renderDiff loaded bumped 10
    ensure (hasSubstr diffText "1 moved") "diff moved count"
    ensure (hasSubstr diffText "== check Nat.add_comm: 565 -> 600") "diff detail header"

    -- 4. Corpus report formatter
    let corpusJson := Json.mkObj [
      ("leaves", Json.arr #[
        Json.mkObj [
          ("shard", toJson (0 : Nat)),
          ("parts", Json.arr #[
            Json.mkObj [("blocks", Json.arr #[toJson (1 : Nat)]),
                        ("report", Json.mkObj [("fft-cost", toJson (700 : Nat))])],
            Json.mkObj [("blocks", Json.arr #[toJson (2 : Nat), toJson (3 : Nat)]),
                        ("status", toJson "refused")]
          ])
        ]
      ])
    ]
    let corpusText ← IO.ofExcept (formatCorpusReport corpusJson.compress)
    ensure (hasSubstr corpusText "FFT corpus initstd shard 0.0 (1 blocks): 700 (expected none)")
      "corpus shard line"
    ensure (hasSubstr corpusText "corpus initstd shard 0.1 (2 blocks) refused")
      "corpus refused line"
    ensure (hasSubstr corpusText "FFT corpus initstd total: 700 (expected none)")
      "corpus total line"
  finally
    try IO.FS.removeDirAll tmp catch _ => pure ()
  IO.println "IxvmBaseline self-tests passed."

end IxvmBaseline

def main (args : List String) : IO UInt32 := do
  match IxvmBaseline.parseArgs args with
  | .error e =>
    IO.eprintln s!"error: {e}\n{IxvmBaseline.usage}"
    return 2
  | .ok .help =>
    IO.println IxvmBaseline.usage
    return 0
  | .ok .selfTest =>
    IxvmBaseline.selfTest
    return 0
  | .ok (.run out recorded?) =>
    IxvmBaseline.runSuite out recorded?
  | .ok (.extract outdir logs outFile?) =>
    let (baseline, stderrLines) ← IxvmBaseline.extractBaseline outdir logs
    for line in stderrLines do IO.eprintln line
    let bytes := IxvmBaseline.encodeBinary baseline
    match outFile? with
    | some path => IO.FS.writeBinFile path bytes
    | none => (← IO.getStdout).write bytes
    return 0
  | .ok (.diff oldPath newPath top) =>
    let old ← IxvmBaseline.loadBaseline oldPath
    let new ← IxvmBaseline.loadBaseline newPath
    IO.println (IxvmBaseline.renderDiff old new top)
    return 0
  | .ok (.showCase basePath label top) =>
    let base ← IxvmBaseline.loadBaseline basePath
    let text ← IO.ofExcept (IxvmBaseline.renderShow base label top)
    IO.println text
    return 0
