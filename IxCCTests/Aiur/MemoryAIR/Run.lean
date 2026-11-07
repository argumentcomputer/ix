import IxCCTests.Aiur.MemoryAIR.Fixtures

namespace IxCCTests.Aiur.MemoryAIR

open _root_.Aiur (G gSize)
open IxCC.Aiur.AIR (Expr Window)
open IxCC.Aiur.AIR.Memory

private def need (count : IO.Ref Nat) (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"Aiur memory AIR regression failed: {label}")
  count.modify (· + 1)

private def accepts (tables : List Table) (limits : Limits := {}) : Bool :=
  match validate limits tables with | .ok _ => true | .error _ => false

private def rejects (tables : List Table) (expected : Error) (limits : Limits := {}) : Bool :=
  match validate limits tables with | .error actual => decide (actual = expected) | .ok _ => false

def run : IO Unit := do
  let count ← IO.mkRef 0
  for (name, table) in [("arbitrary start", arbitraryStart), ("field wrap", wrapped),
      ("signed and zero weight", signed), ("duplicate contents", repeatedContents),
      ("self pointer", selfPointer), ("all padding", allPadding),
      ("empty table", emptyTable), ("zero width", zeroWidth)] do
    need count name (accepts [table])
  need count "no tables" (accepts [])
  need count "same pointer in distinct widths" (accepts distinctBuckets)
  need count "duplicate identical bucket" (rejects [arbitraryStart, arbitraryStart] .duplicateBucket)
  need count "duplicate empty bucket" (rejects [emptyTable, emptyTable] .duplicateBucket)
  need count "duplicate conflicting bucket" (rejects [selfPointer, repeatedContents] .duplicateBucket)
  need count "skipped pointer" (rejects [skippedPointer] (.constraint 0 0))
  need count "repeated pointer" (rejects [repeatedPointer] (.constraint 0 0))
  need count "padding followed by real" (rejects [paddingThenReal] (.constraint 0 0))
  need count "inactive provider" (rejects [inactiveProvider] (.constraint 0 0))
  need count "nonboolean selector" (rejects [nonBoolean] (.selector 0 0))
  need count "short values" (rejects [⟨1, #[⟨1, 1, 7, []⟩]⟩] (.shape 0 0))
  need count "long values" (rejects [⟨1, #[⟨1, 1, 7, [1, 2]⟩]⟩] (.shape 0 0))
  need count "padding shape" (rejects [⟨1, #[⟨0, 0, 7, []⟩]⟩] (.shape 0 0))
  need count "wrapped width rejected" (rejects [⟨gSize.toNat, #[]⟩] .widthLimit
    { maxWidth := gSize.toNat })
  need count "table budget" (rejects [emptyTable] .tableLimit { maxTables := 0 })
  need count "row budget" (rejects [arbitraryStart] .rowLimit { maxRows := 2 })
  need count "total row budget" (rejects distinctBuckets .rowLimit { maxRows := 1 })
  need count "width budget" (rejects [emptyTable] .widthLimit { maxWidth := 0 })
  need count "field budget includes columns" (rejects [selfPointer] .fieldLimit { maxFields := 3 })
  need count "field budget includes padding" (rejects [allPadding] .fieldLimit { maxFields := 7 })
  need count "exact resource boundary" (accepts [selfPointer]
    { maxTables := 1, maxRows := 1, maxWidth := 1, maxFields := 4 })
  need count "zero limits empty" (accepts []
    { maxTables := 0, maxRows := 0, maxWidth := 0, maxFields := 0 })
  let row := realRow 7 42 (0 - 2)
  let next := realRow 100 99
  need count "last-row wrap is masked" ((build 1).check (row.window next false))
  need count "interior wrong next pointer" (!(build 1).check (row.window next true))
  need count "exact negative pull weight"
    ((pull 1).multiplicity.eval (row.window next true) == some 2)
  need count "complete active lookup"
    ((pull 1).arguments.mapM (Expr.eval (row.window next true)) == some [1, 1, 7, 42])
  need count "padding lookup weight"
    ((pull 1).multiplicity.eval ((padding 99 88).window next false) == some 0)
  need count "padding lookup arguments"
    ((pull 1).arguments.mapM (Expr.eval ((padding 99 88).window next false)) == some [0, 0, 0, 0])
  need count "zero width payload"
    ((pull 0).arguments.mapM (Expr.eval ((⟨1, 1, 9, []⟩ : Row).window next false)) == some [1, 0, 9])
  let window : Window := ⟨[3, 4], [5], false, []⟩
  need count "arithmetic expression"
    ((Expr.sub (.mul (.main 0) (.main 1)) (.next 0)).eval window == some 7)
  need count "negative expression" ((Expr.neg (.main 0)).eval window == some (0 - 3))
  need count "missing main column" ((Expr.main 2).eval window == none)
  need count "missing next column" ((Expr.next 1).eval window == none)
  need count "zero product still checks operand" ((Expr.mul (.constant 0) (.main 99)).eval window == none)
  for bucket in [0, 1, 2, 7, 256] do
    let values := (List.range bucket).map G.ofNat
    let row : Row := ⟨0 - 3, 1, 123, values⟩
    need count s!"builder width {bucket}" ((build bucket).width == 3 + bucket)
    need count s!"complete payload width {bucket}"
      ((pull bucket).arguments.mapM (Expr.eval (row.window row false)) ==
        some ([1, G.ofNat bucket, 123] ++ values))
  IO.println s!"aiur-memory-air-tests-ok: {← count.get} assertions, constraints, lookup payloads, shapes and resource boundaries"

end IxCCTests.Aiur.MemoryAIR
