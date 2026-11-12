import Ix.Meta
import Ix.Compile.Equations
import LSpec

/-!
  The stored equations of the fixed-width word operations that
  `ix compile --equations` adds (`Ix.Compile.WordEquations`).

  Every equation of every width elaborates, as a theorem checked by Lean's
  kernel, in the environment of a file that imports nothing but Lean's
  library; and on a source whose root adds two `UInt64`s and converts the sum
  to a `UInt8`, `close` adds exactly the theorems of the operations the
  closure reaches (with `UInt64`'s and `UInt8`'s `ofNat` equation and bridge),
  each to the closure, and none of a width or an operation it does not reach.
  A source without words gets none.
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
    let (_, plainClosed, _, _) ← Ix.Compile.Equations.close plain [`PlainFixture.entry]
    let env ← elaborate dir "Word.lean" wordSource
    let (_, closed, _, failed) ← Ix.Compile.Equations.close env [`WordFixture.entry]
    let added := wordTheorems (closed.map (·.1))
    let names : NameSet := closed.foldl (fun s (n, _) => s.insert n) {}
    let expected : List Name :=
      [`IxWordEquations.UInt64_add, `IxWordEquations.UInt64_toUInt8,
       `IxWordEquations.UInt64_toNat, `IxWordEquations.UInt64_ofNat,
       `IxWordEquations.UInt64_bridge, `IxWordEquations.UInt8_toNat,
       `IxWordEquations.UInt8_ofNat, `IxWordEquations.UInt8_bridge]
    -- At the fixed point an equation is in the closure exactly when its operation is, or, for
    -- the `ofNat` equation and the bridge, when an operation of its width is.
    let reachedWidth := fun (w : Ix.Compile.WordEquations.Width) =>
      (Ix.Compile.WordEquations.equations w).any (names.contains ·.operation)
    let exact := Ix.Compile.WordEquations.widths.all fun w =>
      (Ix.Compile.WordEquations.equations w).all fun e =>
        let isOfNat := e.operation == s!"{w.name}.ofNat".toName
        names.contains e.theoremName ==
          (names.contains e.operation || (isOfNat && reachedWidth w))
    return [
      test "72 equations: per width one per primitive operation (17) and the bridge"
        (all.length == 72),
      test "every equation elaborates as a level-monomorphic theorem" allTheorems,
      test "a closure without words gets no equation"
        (wordTheorems (plainClosed.map (·.1))).isEmpty,
      test "no unfolding-theorem failure on the word source" failed.isEmpty,
      test s!"the word source's closure holds the theorems of its operations: {added}"
        (expected.all added.contains),
      test "an equation is in the closure exactly when its operation (or width) is" exact]

end Tests.Ix.Compile.WordEquations
