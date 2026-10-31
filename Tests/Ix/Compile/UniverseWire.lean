import LSpec
import Ix.CompileM

/-! Native controls for the production preseed wire guard (`checkPreseedUnivs`). The 2^64
overflow boundary itself is not constructed; these controls
exercise all constructors, compressed-count boundaries, depth and integration. -/

namespace Tests.Ix.Compile.UniverseWire

open LSpec
open _root_.Ix (Expr Level Name)
open _root_.Ix.CompileM

private def name := Name.fromLeanName `UniverseWire
private def context : CompileEnv × BlockEnv :=
  (default, { all := {}, current := name, mutCtx := {}, univCtx := [] })

private def raw (action : CompileM α) (state : BlockState := {}) : Except CompileError α × BlockState :=
  (action context).run state

private def successors (count : Nat) : Ixon.Univ := Id.run do
  let mut value := Ixon.Univ.zero
  for _ in [:count] do value := .succ value
  return value

def controls : List (String × Bool) := Id.run do
  let last := (UInt64.size - 1).toUInt64
  let shapes : Array Ixon.Univ := #[.zero, .var 0, .var last, .succ (.var 1),
    .max (.succ .zero) (.var 2), .imax (.var 0) (.succ .zero)]
  let initial : BlockState := {
    refs := #[default]
    univs := #[.var 0]
    univsFinal := true }
  let (accepted, after) := raw (checkPreseedUnivs shapes) initial
  let mut result := [
    ("empty universe list is admitted", (raw (checkPreseedUnivs #[])).1.isOk),
    ("all universe constructors and the largest parameter index are admitted", accepted.isOk),
    ("wire checking retains tables, flags and memo sizes",
      after.refs == initial.refs && after.univs == initial.univs && after.univsFinal == initial.univsFinal &&
      after.univCache.size == initial.univCache.size &&
      after.canonUnivCache.size == initial.canonUnivCache.size)]
  for count in [0, 1, 31, 32, 127, 128, 255, 256, 4096] do
    let value := successors count
    let accepted := (raw (checkPreseedUnivs #[value])).1.isOk
    let exactBytes := (Ixon.deUniv (univSortKey value)).toOption == some value
    result := result ++ [(s!"{count} successors pass admission and byte round-trip", accepted && exactBytes)]
  let roots := #[(Expr.mkSort Level.mkZero, []),
    (Expr.mkSort (Level.mkSucc Level.mkZero), []),
    (Expr.mkSort (Level.mkSucc Level.mkZero), [])]
  let (seeded, state) := raw (preseedExprTables roots)
  result := result ++ [("actual preseed admits canonical values and retains deduplication",
    seeded.isOk && state.univsFinal && state.univs.size == 2 &&
      state.univs.contains .zero && state.univs.contains (.succ .zero))]
  return result

def suite : List TestSeq := controls.map fun (label, ok) => test s!"universe wire: {label}" ok

end Tests.Ix.Compile.UniverseWire
