/-
  pass3-cliques: the clique transport wired into the compile (CQ5.2 (b)), on
  the twins unit (every twin family, the clique families and the clique
  ownership sources, with the rows' prerequisites: `Harness.twinsUnit`).
  Ported in part from the donor's `Tests/Ix/Compile/Pass3Cliques.lean`:

  1. **plans**: every entry of the compile's plan table with its outcome
     (transported, unchanged, baseline with its cause, not encoded), printed;
     coverage: at least one transported well-founded plan;
  2. **rows**: every transported plan whose members are all published has,
     in the output, one `f._ix.row` per row member (`rowMembers`) and one
     `c._ix.src` per encoding constant (`encodingSet`); and every published
     `_ix.row`/`_ix.src` name is one of those (no stray row or copy).

  The unit's other checks are elsewhere, on the same unit: names, decompile
  and the two kernels on every fixture constant and every `_ix` name (rows
  and copies included: row admission in the wired compile) and the block
  failures against their record are `pass3`'s twins unit; the twins under the
  transport are `twins`; the tables' check mode is `pass3-plan-cache`.

  Run with: `lake test -- --ignored pass3-cliques`.
-/
import Tests.Ix.Compile.Harness.Units

open Lean

namespace Tests.Ix.Compile.Pass3Cliques

open Ix.Compile.Pass.Clique (CliqueOutcome rowName srcName rowMembers encodingSet)

def say (s : String) : IO Unit := do
  IO.println s!"[pass3-cliques] {s}"
  (← IO.getStdout).flush

/-- A reserved row or copy name (`f._ix.row`, `c._ix.src`). -/
def isRowOrCopy (n : Ix.Name) : Bool :=
  let s := n.pretty
  s.endsWith "._ix.row" || s.endsWith "._ix.src"

def run : IO UInt32 := do
  let u ← Tests.Ix.Compile.Harness.twinsUnit
  let out ← Tests.Ix.Compile.Harness.compileUnit u
  let cenv := out.cenv
  say s!"{u.closure.length} constants; {out.bytes.size} B, {cenv.ungrounded.size} block failures \
    (checked against their record by `pass3`)"
  let mut problems : Array String := #[]
  -- 1. the plans
  let plans := cenv.p3CliquePlans.toArray.qsort fun a b => a.1.pretty < b.1.pretty
  let mut transported := 0
  for (k, o) in plans do
    let tag := match o with
      | .transported p => s!"TRANSPORTED ({p.encoding.tag}, sigma {p.sigma})"
      | .unchanged enc src => s!"unchanged ({enc.tag}, order by {src.tag})"
      | .baseline enc c why => s!"baseline {c.tag} ({enc.tag}): {why.take 160}"
      | .notEncoded why => s!"not encoded: {why.take 160}"
    say s!"clique {k.pretty}: {tag}"
    if let .transported p := o then
      if p.encoding == .wellFounded then transported := transported + 1
  say s!"{plans.size} plans, {transported} transported well-founded"
  if transported == 0 then problems := problems.push "coverage: no transported well-founded plan"
  -- 2. the rows and copies
  let published : Std.HashSet Ix.Name := out.env.named.fold (fun s n _ => s.insert n) {}
  let mut expected : Std.HashSet Ix.Name := {}
  for (k, o) in plans do
    let .transported p := o | continue
    unless p.all.all published.contains do continue
    match encodingSet cenv.env.get? p with
    | .error e => problems := problems.push s!"{k.pretty}: the encoding set: {e}"
    | .ok enc =>
      for w in (rowMembers p).map rowName ++ enc.toArray.map srcName do
        expected := expected.insert w
        unless published.contains w do
          problems := problems.push s!"{k.pretty}: {w.pretty} is not published"
  let mut rows := 0
  for n in published do
    if isRowOrCopy n then
      rows := rows + 1
      unless expected.contains n do problems := problems.push s!"{n.pretty} is published for no transported plan"
  say s!"rows and copies: {rows} published, {expected.size} expected"
  for p in problems do say s!"FAIL {p}"
  say s!"{problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3Cliques
