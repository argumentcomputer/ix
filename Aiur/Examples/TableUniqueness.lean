import Aiur.TableUniqueness

open Aiur

def main : IO Unit := do
  let cases : List (List (Constant Nat)) := [
    [], [.tuple []], [.tuple [], .tuple []],
    [.tuple [.field 1], .tuple [.field 2]],
    [.tuple [.field 1], .tuple [.field 2], .tuple [.field 1]],
    [.tuple [.field 1, .field 2], .tuple [.field 1, .field 3]],
    [.tuple [.field 1, .field 2], .tuple [.field 1, .field 2]]]
  for rows in cases do
    unless tableRowsNodup rows == decide rows.Nodup do
      throw (IO.userError "table uniqueness differs from the specification")
  let rows : List (Constant Nat) := (List.range 65536).map fun n => .tuple [.field n]
  unless tableRowsNodup rows do throw (IO.userError "distinct range rejected")
  for duplicate in [0, 32768, 65535] do
    unless !(tableRowsNodup (rows ++ [.tuple [.field duplicate]])) do
      throw (IO.userError "duplicate range value accepted")
  let nested : Constant Nat := .tuple [.tuple [.field 7]]
  let mixed := ((List.range 1025).map fun n => (.tuple [.field n] : Constant Nat)) ++ [nested]
  unless tableRowsNodup mixed do throw (IO.userError "mixed unary table rejected")
  unless !(tableRowsNodup (mixed ++ [nested])) do
    throw (IO.userError "non-scalar duplicate ignored")
  IO.println "table uniqueness checks passed"
