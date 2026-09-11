/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Semantics.Flatten

/-! Hash snapshots from the original native derivation. Source evaluation
uses these hashes for its memory buckets; totalization must retain them. -/

open Aiur

namespace Tests.Aiur.SourceValues

def fixtures : Array Value := Id.run do
  let global := Global.init "value"
  let other := global.pushNamespace "child"
  let mut values := #[Value.unit, .tuple #[], .array #[], .ctor global #[], .fn global, .fn other]
  for n in #[0, 1, 255, 256, 65536, 18446744069414584320] do
    let field := Value.field (G.ofNat n)
    let contents := #[Value.unit, field, .pointer n (n + 1)]
    values := values ++ #[field, .pointer n 0, .pointer 0 n, .pointer n n,
      .tuple contents, .array contents, .ctor global contents, .ctor other contents,
      .tuple contents.reverse, .array contents.reverse]
  let mut nested := Value.field 7
  for depth in [:33] do
    nested := match depth % 3 with
      | 0 => .tuple #[nested, .unit]
      | 1 => .array #[.field (G.ofNat depth), nested]
      | _ => .ctor other #[nested, .pointer depth (depth + 1)]
    values := values.push nested
  return values

private def report (values : Array Value) : IO Unit := do
  IO.println s!"SOURCE VALUE HASH FIXTURES {values.size}"
  for h : i in [:values.size] do
    IO.println s!"VALUE {i} HASH {hash values[i]}"

def main : IO Unit := report fixtures

end Tests.Aiur.SourceValues

def main := Tests.Aiur.SourceValues.main
