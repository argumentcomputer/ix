/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Benchmarks.Kernel.CheckIxeRows

/-! # Summaries of an environment check's rows (untrusted tooling)

`kernel-check-ixe --report <rows.jsonl> [top]` prints outcome counts, check
time, decline reasons, and the root causes ranked by how many records they
block. A blocked row names the root record whose failure it inherits (the
environment check follows first causes transitively), so ranking roots by
blocked rows ranks the fixes by reach.

`kernel-check-ixe --summary <rows.jsonl> [--top N] [--json <out>]` writes the
same run as Markdown tables: outcome counts by declaration kind, first-cause
decline and reject reasons, root blockers by records blocked, quantiles and
the slowest rows; `--json` also writes the summary as JSON.

Both were Python scripts until 2026-10-01 (`scripts/check-ixe-report.py`,
`scripts/check-ixe-summary.py`); their output is unchanged
(`Benchmarks.Kernel.CheckIxeRows`). Rows are read as written, so a
compressed row file is decompressed first (`zcat`). -/

namespace Benchmarks.Kernel.CheckIxeReport

open Benchmarks.Kernel.CheckIxeRows

/-- Every row of a row file; `skipBlank` skips blank lines (the summary does,
the report reads every line). -/
def readRows (path : String) (skipBlank : Bool) : IO (Array Value) := do
  let text ← IO.FS.readFile path
  let lines := if skipBlank then (splitLines text).filter (·.trimAscii.toString != "")
    else (text.splitOn "\n").toArray |> fun ls => if ls.back? == some "" then ls.pop else ls
  let mut rows := #[]
  let mut n := 1
  for line in lines do
    match parse line with
    | .ok row => rows := rows.push row
    | .error e => throw <| IO.userError s!"{path}:{n}: {e}"
    n := n + 1
  return rows

def byAddress (rows : Array Value) : Std.HashMap String Value :=
  rows.foldl (fun m r => m.insert (field r "address") r) {}

def secs (micros : Int) (scale : Float := 1e6) : Float := (Float.ofInt micros) / scale

/-- The report's name of a row: its first name, or its address's prefix. -/
def reportName (r : Value) : String :=
  match ((r.get? "names").bind Value.arr?) with
  | some ns => if ns.isEmpty then take 16 (field r "address") else (ns[0]!.str?).getD ""
  | none => take 16 (field r "address")

/-- Decline reasons with an instance-specific suffix, grouped. -/
def group (reason : String) : String :=
  let pfx := "check-ixe: expanded term size exceeds"
  if reason.startsWith pfx then pfx else reason

/-- `--report`, the former `check-ixe-report.py`. -/
def report (path : String) (top : Nat) : IO Unit := do
  let rows ← readRows path false
  let byAddr := byAddress rows
  let outcomes := rows.foldl (fun c r => c.add (field r "outcome")) ({} : Counter)
  IO.println (s!"records {rows.size}: " ++
    ", ".intercalate ((byCountDesc outcomes.items).toList.map fun (k, v) => s!"{k} {v}"))
  -- a recursor checked with its family repeats the pair's time on its own row
  let timed := rows.filter (field · "kind" != "recursor")
  let acceptMicros := (timed.filter (field · "outcome" == "accept")).foldl (· + micros ·) 0
  let allMicros := timed.foldl (· + micros ·) 0
  let readMicros := rows.foldl (· + micros · "readMicros") 0
  IO.println s!"check time: accepts {fixed (secs acceptMicros) 1} s, all {fixed (secs allMicros) 1} s; \
    reading {fixed (secs readMicros) 1} s"
  let reasons := (rows.filter fun r => field r "outcome" == "decline" || field r "outcome" == "reject")
    |>.foldl (fun c r => c.add (group (field r "reason"))) ({} : Counter)
  IO.println "\ndecline and reject reasons:"
  for (reason, count) in (byCountDesc reasons.items).extract 0 top do
    IO.println s!"  {rjust 6 (toString count)}  {reason}"
  let reach := (rows.filter (field · "outcome" == "blocked")).foldl
    (fun c r => c.add (field r "reason")) ({} : Counter)
  IO.println s!"\nroots by blocked records (top {top}):"
  for (root, count) in (byCountDesc reach.items).extract 0 top do
    match byAddr[root]? with
    | none => IO.println s!"  {rjust 6 (toString count)}  {take 16 root}  (not in this environment check)"
    | some r =>
      IO.println s!"  {rjust 6 (toString count)}  {ljust 60 (take 60 (reportName r))}  \
        {field r "outcome"}: {take 70 (group (field r "reason"))}"
  let byReason := reach.items.foldl (init := ({} : Counter)) fun c (root, count) =>
    c.add (match byAddr[root]? with | some r => group (field r "reason") | none => "(outside)") (count + 1)
  IO.println "\nreach by root decline reason (roots plus the records they block):"
  for (reason, count) in (byCountDesc byReason.items).extract 0 top do
    IO.println s!"  {rjust 6 (toString count)}  {take 100 reason}"
  let accepted := timed.filter (field · "outcome" == "accept")
  let slow := ((accepted.mapIdx fun i r => (i, r)).qsort fun a b =>
    micros a.2 > micros b.2 || (micros a.2 == micros b.2 && a.1 < b.1)).extract 0 10
  IO.println "\nslowest accepts:"
  for (_, r) in slow do
    IO.println s!"  {rjust 9 (fixed (secs (micros r) 1e3) 1)} ms  {take 80 (reportName r)}"

/-- `--summary`, the former `check-ixe-summary.py`. -/
def summary (path : String) (top : Nat) (json : Option String) : IO Unit := do
  let rows ← readRows path true
  let byAddr := byAddress rows
  let outcomes := rows.foldl (fun c r => c.add (field r "outcome")) ({} : Counter)
  let mut kinds : Array String := #[]
  let mut byKind : Std.HashMap String Counter := {}
  for r in rows do
    let k := field r "kind"
    unless byKind.contains k do kinds := kinds.push k
    byKind := byKind.insert k ((byKind.getD k {}).add (field r "outcome"))
  let reasons := (rows.filter fun r => field r "outcome" == "decline" || field r "outcome" == "reject")
    |>.foldl (fun c r => c.add (((field r "reason").splitOn " (").headD "")) ({} : Counter)
  let blockers := (rows.filter (field · "outcome" == "blocked")).foldl
    (fun c r => c.add (field r "reason")) ({} : Counter)
  let totalMicros := rows.foldl (· + micros ·) 0
  let readMicros := rows.foldl (· + micros · "readMicros") 0
  let accepted := ((rows.filter (field · "outcome" == "accept")).map (micros ·)).qsort (· < ·)
  let quantile (q : Float) : Float :=
    if accepted.isEmpty then 0.0 else
      let i := (q * accepted.size.toFloat).floor.toUInt64.toNat
      secs accepted[min (accepted.size - 1) i]! 1e3
  let slowest := ((rows.filter (field · "outcome" != "blocked")).mapIdx (fun i r => (i, r))
    |>.qsort (fun a b => micros a.2 > micros b.2 || (micros a.2 == micros b.2 && a.1 < b.1))
    |>.extract 0 10).map (·.2)
  let total := rows.size
  IO.println s!"# Environment check of {pathName path}: {total} declaration rows\n"
  IO.println "| Outcome | Records | Share |\n| --- | ---: | ---: |"
  for (outcome, count) in byCountDesc outcomes.items do
    IO.println s!"| {outcome} | {count} | {fixed (100 * count.toFloat / total.toFloat) 1}% |"
  IO.println s!"\nSum of row timings: checking {fixed (secs totalMicros) 1} s; \
    reading {fixed (secs readMicros) 1} s. \
    Family/recursor rows repeat admission timings; these are not wall times."
  if accepted.isEmpty then IO.println "" else
    let topMicros := slowest.foldl (· + micros ·) 0
    IO.println s!"Accepted row time: median {fixed (quantile 0.5) 2} ms, p90 {fixed (quantile 0.9) 2} ms, \
      p99 {fixed (quantile 0.99) 1} ms; the 10 slowest rows account for \
      {fixed (100 * (Float.ofInt topMicros) / (Float.ofInt (max totalMicros 1))) 0}% of summed checking time\n"
  IO.println "| Kind | accept | decline | reject | blocked |\n| --- | ---: | ---: | ---: | ---: |"
  let kindTotal (k : String) : Nat := ((byKind.getD k {}).items.map (·.2)).foldl (· + ·) 0
  for (kind, _) in byCountDesc (kinds.map fun k => (k, kindTotal k)) do
    let c := byKind.getD kind {}
    IO.println s!"| {kind} | {c.get "accept"} | {c.get "decline"} | {c.get "reject"} | {c.get "blocked"} |"
  IO.println s!"\n## First-cause reasons (top {top})\n"
  IO.println "| Records | Reason |\n| ---: | --- |"
  for (reason, count) in (byCountDesc reasons.items).extract 0 top do
    IO.println s!"| {count} | {reason} |"
  IO.println s!"\n## Root blockers by records blocked (top {top})\n"
  IO.println "| Blocked | Root | Kind | Outcome | Reason |\n| ---: | --- | --- | --- | --- |"
  let mut topBlockers : Array Value := #[]
  for (address, count) in (byCountDesc blockers.items).extract 0 top do
    let root := byAddr[address]?
    let rootNames := (root.map names).getD #[]
    let name := if rootNames.isEmpty then take 16 address else ", ".intercalate (rootNames.toList.take 2)
    let get (k : String) : String := match root with
      | some r => if (r.get? k).isSome then field r k else "?"
      | none => "?"
    IO.println s!"| {count} | {name} | {get "kind"} | {get "outcome"} | {get "reason"} |"
    let rootFields := match root with | some (.obj kvs) => kvs | _ => #[]
    topBlockers := topBlockers.push
      (Value.mkObj (#[("address", .str address), ("blocked", .int count)] ++ rootFields))
  IO.println "\n## Slowest row timings\n"
  IO.println "| Seconds | Outcome | Kind | Name |\n| ---: | --- | --- | --- |"
  for row in slowest do
    let ns := names row
    let name := if ns.isEmpty then take 16 (field row "address") else ns[0]!
    IO.println s!"| {fixed (secs (micros row)) 2} | {field row "outcome"} | {field row "kind"} | {name} |"
  if let some out := json then
    let counterObj (c : Counter) : Value := .obj (c.items.map fun (k, n) => (k, .int n))
    let summaryJson : Value := .obj #[
      ("input", .str (pathStr path)), ("records", .int total),
      ("outcomes", counterObj outcomes),
      ("byKind", .obj (kinds.map fun k => (k, counterObj (byKind.getD k {})))),
      ("reasons", .arr ((byCountDesc reasons.items).map fun (k, n) => .arr #[.str k, .int n])),
      ("rootBlockers", .arr topBlockers),
      ("checkingSeconds", .float (secs totalMicros)), ("readingSeconds", .float (secs readMicros)),
      ("timingScope", .str "sum of row timings; paired admissions counted twice; not wall time"),
      ("acceptedMillis", .obj #[("median", .float (quantile 0.5)), ("p90", .float (quantile 0.9)),
        ("p99", .float (quantile 0.99))]),
      ("slowest", .arr (slowest.map fun row => .obj #[
        ("seconds", .float (secs (micros row))),
        ("names", .arr (((names row).toList.take 1).toArray.map .str)),
        ("outcome", .str (field row "outcome"))]))]
    IO.FS.writeFile out (summaryJson.dumps 1 ++ "\n")

def usage : String :=
  "usage: kernel-check-ixe --report <rows.jsonl> [top]\n       \
   kernel-check-ixe --summary <rows.jsonl> [--top N] [--json <out.json>]"

def runReport : List String → IO UInt32
  | [path] => do report path 30; return 0
  | [path, top] => do
    let some n := top.toNat? | IO.eprintln usage; return 2
    report path n; return 0
  | _ => do IO.eprintln usage; return 2

def runSummary (args : List String) : IO UInt32 := do
  let rec parse : List String → Option String → Nat → Option String → Option (String × Nat × Option String)
    | [], some p, top, json => some (p, top, json)
    | "--top" :: n :: rest, p, _, json => n.toNat?.bind fun t => parse rest p t json
    | "--json" :: out :: rest, p, top, _ => parse rest p top (some out)
    | arg :: rest, none, top, json => if arg.startsWith "-" then none else parse rest (some arg) top json
    | _, _, _, _ => none
  let some (path, top, json) := parse args none 25 none | IO.eprintln usage; return 2
  summary path top json
  return 0

end Benchmarks.Kernel.CheckIxeReport
