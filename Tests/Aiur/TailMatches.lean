/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Stages.Source

/-! Native syntax snapshots captured before replacing partial tail-match
restoration. Every term and pattern constructor occurs. Tail positions,
non-tail subexpressions, distinct local names and nested matches are covered. -/

open Aiur Aiur.Source

namespace Tests.Aiur.TailMatches

private def eta (name : Local) (value : Term) : Term :=
  .let (.var name) value (.var name)

private def constructors (value : Term) : Array Term :=
  let global := Global.init "fixture"
  #[.unit, .var (.str "x"), .ref global, .field 7,
    .tuple #[value], .array #[value], .ret value,
    .let .wildcard value value, .match value [(.wildcard, value)],
    .app global [value] .normal, .app global [value] .unconstrained,
    .app global [value] .inlined,
    .add value value, .sub value value, .mul value value, .eqZero value,
    .proj value 0, .get value 0, .slice value 0 1, .set value 0 value,
    .store value, .load value, .ptrVal value, .ann .field value,
    .assertEq value value none value, .assertEq value value (some "check") value,
    .ioGetInfo value value, .ioSetInfo value value value value value,
    .ioRead value value 1, .ioWrite value value value,
    .u8BitDecomposition value, .u8ShiftLeft value, .u8ShiftRight value,
    .u8Xor value value, .u8Add value value, .u8Mul value value,
    .u8Sub value value, .u8And value value, .u8Or value value,
    .u8LessThan value value, .u32LessThan value value,
    .u8XorSplit7 value value, .u8XorSplit4 value value,
    .unconstrainedU32Add value value, .unconstrainedU32Add3 value value value,
    .u32ToField value, .unconstrainedBigUintDivMod value value,
    .unconstrainedGToBytes value, .unconstrainedGInverse value,
    .u8Lit 255, .u8RangeCheck value value, .toField value,
    .u8FromFieldUnsafe value, .debug "message" none value,
    .debug "message" (some value) value]

private def patterns : Array Pattern :=
  #[.var (.str "x"), .var (.idx 0), .wildcard,
    .ref (Global.init "Ctor") [.var (.str "x")], .field 7,
    .tuple #[.var (.str "x")], .array #[.wildcard],
    .or (.field 7) (.var (.str "x")), .pointer (.var (.str "x"))]

def fixtures : Array Term := Id.run do
  let name : Local := .str "x"
  let wrapped := eta name (.field 7)
  let mut terms := #[]
  for term in constructors wrapped do
    terms := terms ++ #[term, eta name term,
      .let (.var name) term (.var (.str "y")),
      .let .wildcard wrapped (eta name term)]
  for pattern in patterns do
    terms := terms ++ #[.let pattern wrapped wrapped,
      .match wrapped [(pattern, wrapped), (.wildcard, eta name (.ret wrapped))]]
  for x in #[Local.str "x", .str "0", .idx 0, .idx 1] do
    for y in #[Local.str "x", .str "0", .idx 0, .idx 1] do
      terms := terms.push (.let (.var x) wrapped (.var y))
  terms := terms ++ #[.match wrapped [], .match wrapped [(.field 9, wrapped)]]
  let mut nested := wrapped
  for depth in [:25] do
    nested := eta (.idx depth)
      (.match wrapped [(.field 7, nested), (.wildcard, eta name (.ret wrapped))])
    terms := terms.push nested
  return terms

private def report (terms : Array Term) : IO Unit := do
  IO.println s!"TAIL MATCH FIXTURES {terms.size}"
  for h : i in [:terms.size] do
    IO.println s!"TERM {i} {(repr terms[i].restoreTailMatches).pretty 1000000}"

def main : IO Unit := report fixtures

end Tests.Aiur.TailMatches

def main := Tests.Aiur.TailMatches.main
