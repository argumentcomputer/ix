import Ix.Meta
import Ix.Compile.Equations
import LSpec

/-!
  The stored equations of the fixed-width word operations that
  `ix compile` adds by default with the equations (`Ix.Compile.WordEquations`).

  Every equation of every width elaborates, as a theorem checked by Lean's
  kernel, in the environment of a file that imports nothing but Lean's
  library; and on a source whose root adds two `UInt64`s and converts the sum
  to a `UInt8`, `close` adds exactly the theorems of the operations the
  root reaches outside theorems (with `UInt64`'s and `UInt8`'s `ofNat`, whose theorem is
  the bridge), each to the closure, and none of a width or an operation it does not reach
  (not `UInt64.toNat`, which the closure holds only inside `UInt64.toUInt8`'s own body),
  and the output's `theorems` list (`ix/compile-equations/2`) names each with
  its operation. A source without words gets none.
-/

open Lean LSpec

namespace Tests.Ix.Compile.WordEquations

def wordSource : String := "namespace WordFixture

def entry (a b : Nat) : Nat := ((a.toUInt64 + b.toUInt64).toUInt8).toNat

end WordFixture
"

def plainSource : String := "namespace PlainFixture

def entry (a b : Nat) : Nat := a + b

end PlainFixture
"

def elaborate (dir : System.FilePath) (file : String) (text : String) : IO Environment := do
  let path := dir / file
  IO.FS.writeFile path text
  getFileEnv path

def wordTheorems (names : List Name) : List Name :=
  names.filter fun n => n.getPrefix == `IxWordEquations

def suite : IO (List LSpec.TestSeq) := do
  IO.FS.withTempDir fun dir => do
    let plain ← elaborate dir "Plain.lean" plainSource
    let all := Ix.Compile.WordEquations.all
    let withAll ← Ix.Compile.WordEquations.add plain all
    let allTheorems := all.all fun e =>
      match withAll.find? e.theoremName with
      | some (.thmInfo t) => t.levelParams.isEmpty
      | _ => false
    let (_, plainClosed, _, _) ← Ix.Compile.Equations.close plain [`PlainFixture.entry] (words := true)
    let env ← elaborate dir "Word.lean" wordSource
    let (_, closed, _, failed) ← Ix.Compile.Equations.close env [`WordFixture.entry] (words := true)
    let (_, closedOff, _, _) ← Ix.Compile.Equations.close env [`WordFixture.entry]
    let added := wordTheorems (closed.map (·.1))
    let names : NameSet := closed.foldl (fun s (n, _) => s.insert n) {}
    let expected : List Name :=
      [`IxWordEquations.UInt64_add, `IxWordEquations.UInt64_toUInt8,
       `IxWordEquations.UInt64_ofNat, `IxWordEquations.UInt8_toNat, `IxWordEquations.UInt8_ofNat]
    -- The walk: the operations the root reaches outside theorems, not entering an operation.
    let reached := Ix.Compile.WordEquations.reachedOutsideTheorems env [`WordFixture.entry]
    let reachedOps : List Name := [`UInt64.add, `UInt64.ofNat, `UInt64.toUInt8, `UInt8.toNat]
    let exact := reachedOps.all reached.contains && reached.toList.length == reachedOps.length &&
      names.contains `UInt64.toNat
    -- The output names every word equation of the closure with its operation, kind `word`.
    let proposals := Ix.Compile.Equations.theorems (closed.map (·.1))
    let json := Ix.Compile.Equations.toJson #[] proposals #[]
    let listed : List (String × String × String) :=
      match json.getObjValAs? (Array Json) "theorems" with
      | .ok rows => rows.toList.filterMap fun row =>
          match row.getObjValAs? String "kind", row.getObjValAs? String "subject",
              row.getObjValAs? String "theorem" with
          | .ok k, .ok s, .ok t => some (k, s, t)
          | _, _, _ => none
      | .error _ => []
    let named := Ix.Compile.WordEquations.all.filter (added.contains ·.theoremName)
    let subjects : List String := listed.map (·.2.1)
    let sorted : Bool := subjects == subjects.mergeSort (fun a b => decide (a ≤ b))
    return [
      test "68 equations: per width one per primitive operation (17; `ofNat`'s is the bridge)"
        (all.length == 68),
      test "every equation elaborates as a level-monomorphic theorem" allTheorems,
      test "a closure without words gets no equation"
        (wordTheorems (plainClosed.map (·.1))).isEmpty,
      test "no unfolding-theorem failure on the word source" failed.isEmpty,
      test s!"the word source's closure holds the theorems of its operations and bridges, and only \
          those: {added}"
        (expected.all added.contains && added.length == expected.length),
      test s!"the walk reaches four operations outside theorems, not UInt64.toNat (in the closure, \
          inside UInt64.toUInt8's body): {reached.toList}" exact,
      test s!"the output's theorems name each equation of the closure with its operation: {listed}"
        (listed.length == added.length && named.all fun e =>
          listed.contains ("word", e.operation.toString, e.theoremName.toString)),
      test "the output's theorems are sorted by subject" sorted,
      test "with words off (`ix compile --no-word-equations`) the word source gets no equation"
        (wordTheorems (closedOff.map (·.1))).isEmpty,
      test "a closure without words gets no theorem proposal"
        (Ix.Compile.Equations.theorems (plainClosed.map (·.1))).isEmpty]

end Tests.Ix.Compile.WordEquations
