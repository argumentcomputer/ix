module

import Ix.Cli.CheckCmd

/-!
`.ixes` manifest parser: the optional trailing sections (bisection tree,
measured peaks) and the strict end-of-input check, on synthetic manifests
built byte by byte so no environment is needed.
-/

namespace Tests.Ix.Ixes

open Ix.Cli.CheckCmd (AggregationTree parseIxesManifest)

private def u32 (n : Nat) : ByteArray := n.toUInt32.toLEBytes
private def u64 (n : Nat) : ByteArray := n.toUInt64.toLEBytes

private def fakeAddr (tag : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate 32 tag)

/-- One shard record: `id ‖ heartbeats ‖ own_size ‖ cross_ingress ‖
    assumption_root(absent) ‖ blocks(1) ‖ foreign_blocks(0)`. -/
private def record (id : Nat) : ByteArray :=
  u32 id ++ u64 (100 + id) ++ u64 (200 + id) ++ u64 0
    ++ ByteArray.mk #[0] ++ u32 1 ++ fakeAddr (id.toUInt8 + 1) ++ u32 0

/-- Records only: the layout every writer starts with. -/
private def recordsOnly : ByteArray :=
  "IXES".toUTF8 ++ ByteArray.mk #[0, 0, 0, 0] ++ ByteArray.mk (Array.replicate 16 0)
    ++ u32 2 ++ record 0 ++ record 1

/-- `node(leaf 1, leaf 0)`: deliberately not the balanced fallback. -/
private def treeSection : ByteArray :=
  ByteArray.mk #[1, 1, 0] ++ u32 1 ++ ByteArray.mk #[0] ++ u32 0

private def expect (name : String) (cond : Bool) : IO Bool := do
  if cond then IO.println s!"  ✓ {name}" else IO.eprintln s!"  ✗ {name}"
  pure cond

private def isErrorContaining (r : Except String α) (needle : String) : Bool :=
  match r with
  | .error e => (e.splitOn needle).length > 1
  | .ok _ => false

public def suite : IO UInt32 := do
  IO.println "ixes-manifest"
  let balanced := AggregationTree.node (.leaf 0) (.leaf 1)
  let custom := AggregationTree.node (.leaf 1) (.leaf 0)
  let mut ok := true
  -- 1. Records only: balanced tree fallback, unmeasured peaks.
  let r1 := parseIxesManifest recordsOnly
  ok := (← expect "records-only parses" r1.toBool) && ok
  if let .ok v := r1 then
    ok := (← expect "records-only: two shards, one block each"
      (v.shards.size == 2 && v.shards.all (·.size == 1))) && ok
    ok := (← expect "records-only: balanced tree fallback" (v.aggregationTree == balanced)) && ok
    ok := (← expect "records-only: peaks unmeasured" (v.measuredPeakBytes == #[0, 0])) && ok
  -- 2. Explicit zero presence bytes for both sections (what `ix shard`
  --    writes for a planner manifest with no tree).
  let r2 := parseIxesManifest (recordsOnly ++ ByteArray.mk #[0, 0])
  ok := (← expect "zero presence bytes parse" r2.toBool) && ok
  if let .ok v := r2 then
    ok := (← expect "zero presence: balanced tree, zero peaks"
      (v.aggregationTree == balanced && v.measuredPeakBytes == #[0, 0])) && ok
  -- 3. Tree, then peaks.
  let withPeaks := recordsOnly ++ treeSection ++ ByteArray.mk #[1] ++ u64 4096 ++ u64 0
  let r3 := parseIxesManifest withPeaks
  ok := (← expect "tree + peaks parse" r3.toBool) && ok
  if let .ok v := r3 then
    ok := (← expect "tree section is honoured" (v.aggregationTree == custom)) && ok
    ok := (← expect "peaks read in id order" (v.measuredPeakBytes == #[4096, 0])) && ok
  -- 4. Tree, no peaks section at all (pre-peaks writer).
  let r4 := parseIxesManifest (recordsOnly ++ treeSection)
  ok := (← expect "tree without peaks section parses" r4.toBool) && ok
  if let .ok v := r4 then
    ok := (← expect "tree without peaks: zero peaks" (v.measuredPeakBytes == #[0, 0])) && ok
  -- 5. Strictness: anything after the last known section is an error.
  ok := (← expect "trailing byte after peaks is rejected"
    (isErrorContaining (parseIxesManifest (withPeaks ++ ByteArray.mk #[7])) "trailing")) && ok
  ok := (← expect "bad peaks presence tag is rejected"
    (isErrorContaining (parseIxesManifest (recordsOnly ++ treeSection ++ ByteArray.mk #[2])) "presence tag")) && ok
  ok := (← expect "truncated peaks section is rejected"
    (isErrorContaining (parseIxesManifest (recordsOnly ++ treeSection ++ ByteArray.mk #[1] ++ u64 1)) "truncated")) && ok
  pure (if ok then 0 else 1)

end Tests.Ix.Ixes
