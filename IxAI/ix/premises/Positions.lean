import Lean

/-!
# Source positions of library theorems

`lean --run Positions.lean OUT MODULE…`

Writes `NAME<TAB>LINE<TAB>COLUMN<TAB>STEPS` for every theorem `Extract.lean` lists as a library
theorem: the start of its declaration range. A theorem without a range of its own (an equation
lemma, an `injEq`, …) takes the range of its nearest name prefix declared in the same module, and
`STEPS` counts the prefixes dropped; `-1` marks a theorem for which no range was found.

The position of a constant in a module's `constNames` is not its source order, so "declared
earlier in the same module" has to be decided from these positions.
-/

open Lean

def rangeOf (env : Environment) (n : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env n <|> declRangeExt.find? (level := .server) env n
    <|> declRangeExt.find? (level := .private) env n

def main (args : List String) : IO UInt32 := do
  let out :: mods := args | IO.eprintln "usage: Positions OUT MODULE…"; return 2
  initSearchPath (← findSysroot)
  unsafe Lean.enableInitializersExecution
  let env ← importModules (mods.toArray.map ({ module := ·.toName })) {} (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  let names := env.header.moduleNames
  let mut own := 0
  let mut viaPrefix := 0
  let mut missing := 0
  for i in [:names.size] do
    for n in env.header.moduleData[i]!.constNames do
      let some (.thmInfo _) := env.find? n | continue
      if n.isInternalDetail then continue
      let mut cur := n
      let mut steps := 0
      let mut found : Option DeclarationRanges := none
      while found.isNone && !cur.isAnonymous do
        if env.getModuleIdxFor? cur == some i then found := rangeOf env cur
        if found.isNone then
          cur := cur.getPrefix
          steps := steps + 1
      match found with
      | some d =>
        h.putStrLn s!"{n}\t{d.range.pos.line}\t{d.range.pos.column}\t{steps}"
        if steps == 0 then own := own + 1 else viaPrefix := viaPrefix + 1
      | none =>
        h.putStrLn s!"{n}\t-1\t-1\t-1"
        missing := missing + 1
  h.flush
  IO.println s!"own range {own}, range of a prefix {viaPrefix}, none {missing}"
  return 0
