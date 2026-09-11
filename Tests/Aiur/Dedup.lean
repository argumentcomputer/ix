/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Aiur.DedupFixtures
import Ix.Aiur.Semantics.BytecodeEval

namespace AiurTests.Dedup

open Aiur Aiur.Bytecode

/-- Full syntax and index maps captured before adding checked renaming. -/
def snapshot : IO Unit := do
  for (name, source) in fixtures do
    let (target, rename) := source.deduplicate
    IO.println s!"PROGRAM {name} FUNCTIONS {source.functions.size} -> {target.functions.size}"
    IO.println s!"RENAME {(Array.range (source.functions.size + 3)).map rename}"
    IO.println s!"MEMORY {target.memorySizes}"
    for i in [:target.functions.size] do
      IO.println s!"FUNCTION {i} {repr target.functions[i]!}"

private def checkRejected (label : String) (source candidate : Toplevel)
    (rename : FunIdx → FunIdx) : IO Unit := do
  if validatesRenaming source candidate (boundedRenaming source rename) then
    throw (IO.userError s!"invalid deduplication accepted: {label}")
  let (selected, actualRename) := checkedRenaming source candidate rename
  unless reprStr selected == reprStr source do
    throw (IO.userError s!"fallback changed the original program: {label}")
  for i in [:source.functions.size + 3] do
    unless actualRename i == i do
      throw (IO.userError s!"fallback changed function index {i}: {label}")
  IO.println s!"PASS {label}: rejected and original program retained"

private def checkExecution (label : String) (source : Toplevel) (args expected : Array G)
    (fuel : Nat) (initial final : IOBuffer) : IO Unit := do
  let (target, rename) := source.deduplicate
  unless target.functions.size < source.functions.size do
    throw (IO.userError s!"execution fixture did not merge functions: {label}")
  for (program, function) in #[(source, 0), (target, rename 0)] do
    match Eval.runFunction program function args initial fuel with
    | .error error => throw (IO.userError s!"{label}: {repr error}")
    | .ok (output, io) =>
      unless output == expected && io == final do
        throw (IO.userError s!"execution or final I/O changed: {label}")
  IO.println s!"PASS {label}: original and merged execution agree"

/-- The caller loads memory created by a merged callee, then appends to its
I/O output. Pre-existing arena contents and key information must survive. -/
private def stateful : Toplevel :=
  let worker : Function := ⟨⟨#[.const 0, .store #[0], .load 1 2, .ioWrite 1 #[3]],
    .return 0 #[2, 3]⟩, layout 1, false, false⟩
  let main (target : Nat) : Function := ⟨⟨#[.const 7, .call target #[0] 2 false,
    .load 1 1, .const 0, .ioWrite 4 #[3]], .return 0 #[2, 3]⟩, layout, true, false⟩
  program #[main 2, main 3, worker, worker]

def run : IO Unit := do
  for (name, source) in fixtures do
    let (candidate, rename) := source.deduplicateCandidate
    unless validatesRenaming source candidate (boundedRenaming source rename) do
      throw (IO.userError s!"original partition candidate declined: {name}")
  IO.println s!"PASS {fixtures.size} original partition candidates: accepted"

  let base := constant 7 true
  let source := program #[base, base, base]
  let variants : Array (String × Function) := #[
    ("changed-constant", constant 8 true),
    ("changed-return-value", { base with body := { base.body with ctrl := .return 0 #[1] } }),
    ("changed-return-selector", { base with body := { base.body with ctrl := .return 1 #[0] } }),
    ("changed-input-arity", { base with layout := layout 1 }),
    ("changed-selector-layout", { base with layout := { layout with selectors := 3 } }),
    ("changed-auxiliary-layout", { base with layout := { layout with auxiliaries := 9 } }),
    ("changed-lookup-layout", { base with layout := { layout with lookups := 6 } })]
  for (label, changed) in variants do
    checkRejected label source (program #[changed]) (fun _ => 0)
  checkRejected "missing-target" source (program #[]) (fun _ => 0)
  checkRejected "invalid-call-domain-expanded" source (program #[base, base, base, base]) (fun _ => 0)
  checkRejected "out-of-range-target" source (program #[base]) (fun _ => 1)

  let (candidate, rename) := withContinuations.deduplicateCandidate
  let original := candidate.functions[0]!
  let .matchContinue idx branches fallback out aux lookups cont := original.body.ctrl
    | throw (IO.userError "continuation fixture changed")
  let mutations : Array (String × Ctrl) := #[
    ("changed-call-target", .matchContinue idx branches fallback out aux lookups
      { cont with ops := #[.call 0 #[2] 1 false] }),
    ("changed-call-arguments", .matchContinue idx branches fallback out aux lookups
      { cont with ops := #[.call 1 #[] 1 false] }),
    ("changed-call-output-size", .matchContinue idx branches fallback out aux lookups
      { cont with ops := #[.call 1 #[2] 2 false] }),
    ("removed-early-return", .matchContinue idx branches none out aux lookups cont)]
  for (label, ctrl) in mutations do
    checkRejected label withContinuations
      { candidate with functions := candidate.functions.set! 0 { original with body := { original.body with ctrl } } }
      rename

  checkExecution "yield-to-continuation" withContinuations #[0] #[7] 1 default default
  checkExecution "early-return-skips-continuation" withContinuations #[5] #[5] 0 default default
  let initial := (default : IOBuffer).extend 0 #[42] #[99]
  let final := { initial with data := initial.data.insert 0 #[99, 7, 7] }
  checkExecution "callee-memory-and-io" stateful #[] #[7, 7] 1 initial final
  checkExecution "merged-public-entry" source #[] #[7] 0 default default
  IO.println s!"deduplication: {fixtures.size} accepted candidates, {variants.size + 3 + mutations.size} rejected candidates, 4 execution cases"

end AiurTests.Dedup

def main (args : List String) : IO Unit :=
  match args with
  | [] => AiurTests.Dedup.run
  | ["--snapshot"] => AiurTests.Dedup.snapshot
  | _ => throw (IO.userError "usage: aiur-dedup-tests [--snapshot]")
