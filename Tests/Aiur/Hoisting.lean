/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur

/-! Effect-order regressions for argument normalization. These use the
actual source compiler, both reference evaluators and the native executor. -/

open Aiur Aiur.Source

namespace Tests.Aiur.Hoisting

private def write (n : Nat) (ret : Term) : Term :=
  .ioWrite (.field 0) (.array #[.field (G.ofNat n)]) ret

private def program (body : Term) (output : Typ)
    (safe : sigPointerFree [] output = true) : Toplevel :=
  ⟨#[], #[], #[Function.monoEntry (Global.init "test") [] output body safe], false⟩

private def returningHelper (early : Bool) : Toplevel :=
  let x : Term := .var (.str "x")
  let body := if early then
      .let (.var (.str "y"))
        (.match x [(.field 0, .ret (.field 7)), (.wildcard, .field 4)])
        (.add (.var (.str "y")) (.field 1))
    else .ret (.add x (.field 1))
  let helper := Function.monoNonEntry (Global.init "helper") [(.str "x", .field)] .field body
  let main := program (.add (.app (Global.init "helper") [.field 0] .inlined) (.field 3))
    .field (by simp [sigPointerFree, Typ.hasPointer])
  { main with functions := #[helper] ++ main.functions }

def fixtures : Array (String × Toplevel × Array Aiur.G × Array Aiur.G) := #[
  ("set-argument-order", program
    (.set (.let .wildcard (write 1 .unit) (.array #[.field 5])) 0
      (.let .wildcard (write 2 .unit) (.field 9))) (.array .field 1)
    (by simp [sigPointerFree, Typ.hasPointer]), #[9], #[2, 1]),
  ("operand-core-before-next-frames", program
    (.add (write 1 (.field 3)) (.let .wildcard (write 2 .unit) (.field 4))) .field
    (by simp [sigPointerFree, Typ.hasPointer]), #[7], #[1, 2]),
  ("write-before-continuation", program
    (write 1 (.let .wildcard (write 2 .unit) (.field 3))) .field
    (by simp [sigPointerFree, Typ.hasPointer]), #[3], #[1, 2]),
  ("tuple-element-order", program
    (.tuple #[write 1 (.field 3), .let .wildcard (write 2 .unit) (.field 4)])
    (.tuple #[.field, .field]) (by simp [sigPointerFree, Typ.hasPointer]), #[3, 4], #[1, 2]),
  ("array-element-order", program
    (.array #[write 1 (.field 3), .let .wildcard (write 2 .unit) (.field 4)])
    (.array .field 2) (by simp [sigPointerFree, Typ.hasPointer]), #[3, 4], #[1, 2]),
  ("lexical-binding-scope", program
    (.let (.var (.str "x")) (.field 10)
      (.add (.let (.var (.str "x")) (.field 3) (.var (.str "x"))) (.var (.str "x"))))
    .field (by simp [sigPointerFree, Typ.hasPointer]), #[13], #[]),
  ("inline-tail-return-boundary", returningHelper false, #[4], #[]),
  ("inline-early-return-boundary", returningHelper true, #[10], #[]),
  ("debug-value-before-continuation", program
    (.debug "debug-value-before-continuation" (some (write 1 (.field 4)))
      (write 2 (.field 3))) .field (by simp [sigPointerFree, Typ.hasPointer]),
    #[3], #[1, 2])]

def main : IO Unit := do
  let mut failures := 0
  for (label, source, expected, effects) in fixtures do
    let decls ← IO.ofExcept (source.mkDecls.mapError toString)
    let (value, io) ← IO.ofExcept
      ((Source.Eval.runFunction decls (Global.init "test") [] default 100).mapError reprStr)
    unless flattenValue decls (fun _ => none) value == expected && io.data.getD 0 #[] == effects do
      throw (IO.userError s!"invalid source fixture: {label}")
    let (interpreted, state) := Aiur.runFunction decls (Global.init "test") [] default
    let interpreted ← IO.ofExcept interpreted
    unless flattenValue decls (fun _ => none) interpreted == expected && state.ioBuffer == io do
      throw (IO.userError s!"source interpreters disagree: {label}")
    match source.compile with
    | .error error =>
      failures := failures + 1
      IO.println s!"FAIL {label}: compilation: {error}"
    | .ok compiled =>
      let some index := compiled.getFuncIdx `test
        | throw (IO.userError s!"missing function: {label}")
      let reference := (Bytecode.Eval.runFunction compiled.bytecode index #[] default 100).mapError reprStr
      let native := (compiled.bytecode.execute index #[] default).map fun (output, state, _) => (output, state)
      for (engine, result) in #[("bytecode reference", reference), ("native", native)] do
        match result with
        | .error error =>
          failures := failures + 1
          IO.println s!"FAIL {label}: {engine}: {error}"
        | .ok (output, actualIo) =>
          if output == expected && actualIo == io then IO.println s!"PASS {label}: {engine}"
          else
            failures := failures + 1
            IO.println s!"FAIL {label}: {engine}: output {output}, effects {actualIo.data.getD 0 #[]}; expected {expected}, {effects}"
  unless failures == 0 do throw (IO.userError s!"{failures} hoisting regressions")

end Tests.Aiur.Hoisting

def main := Tests.Aiur.Hoisting.main
