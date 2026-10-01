/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Std.Data.HashMap
import Std.Data.HashSet
import Tests.Ix.Kernel.KernelLayout

/-! # The kernel's import-layering fence (`kernel-layering`)

Derived from con-leche's `tests/layering.sh` (Apache-2.0), modified; see
`Ix/Kernel/NOTICE`. Until 2026-10-01 this was `scripts/layering.sh`, a
Python program in a shell wrapper, as upstream's is.

It covers the checker and the theory under `Ix/Kernel/`, each file
classified by its path (`Tests.Ix.Kernel.KernelLayout`, whose table
`topLevel` must classify every file under `Ix/Kernel/`), and rejects these
import edges:

  1. CHECKER→THEORY: no module of the checker (`KernelLayout.Part.checker`:
     the flattened implementation, `Cached/*`, `Frontend/*`) imports
     `Ix.Kernel.{Verify,SetTheory,Model,SetModel,Semantics,Term}.*`.
  2. BASE→MODEL: no base module (everything outside the model lane
     `Ix/Kernel/Model{,/*}` and the capstone assembly `MainTheorem`,
     `Verify/Cached{,/*}`) imports the model lane.
  3. THE RULES FENCE: `Ix/Kernel/Rules/*` and `Ix/Kernel/Model/Rules/*`
     (except `Model.Rules.Recompose`) do not directly import
     `Ix.Kernel.{Core,TypeChecker,CoreIO,DeclCheck,Checker*}` or `Cached*`.
  4. THE RULES CLOSURE: the elaboration closure of those modules (direct
     imports, then `public import`s) reaches exactly the five recorded
     doors (`rulesClosureDoors`). A new door is a regression; a door no
     longer reached is progress to record by deleting it there. Both fail.
  5. THE BOUNDARY: a covered module imports only covered modules, `Init`,
     `Std` and `Lean` (the last at elaboration time; the Lean import audit
     checks that part). Ix's boundary (`Ixon`, `Audit`, `Ingress`,
     `Egress`, `Ref`, `Search`) imports the kernel, never the other way
     round.

Every import kind is an edge: `public`, `private`, `meta`, `import all`.
Lake gives no import barrier between `lean_lib`s of one package, so this
fence, not the library split, is the fence. The scan is upstream's: block
comments `/-…-/` are stripped first (shortest match, not nested), then every
line that begins, after blanks, with `public`/`private`/`meta` keywords and
`import` (with `all`) names one import (Python `re`'s grammar, with its
Unicode whitespace). Changes from upstream: the checked files and their
classes come from the repository's own layout; upstream's dead base→model
clause (it compared with a lane that never occurs) is repaired, with the
capstone assembly classified by path as upstream's comment states; the
boundary clause is added; an empty `Ix/Kernel/` passes vacuously, and the
rules-closure clause waits until a rules module exists.

Usage: `lake exe kernel-layering [--list]`, from the repository root
(`--list` prints the base→model edges, every rules module's elaboration
closure with its doors marked `!`, and one witnessing chain per door).
Exit code 0 on success, 1 on a finding.
-/

namespace Tests.Ix.Kernel.Layering

open Tests.Ix.Kernel.KernelLayout

/-! ## The scan -/

/-- Strip block comments as Python's `re.sub(r'/-.*?-/', '', src, flags=re.S)`
does: the shortest `/-` … `-/` match, left to right, not nested. -/
def stripBlockComments (src : Array Char) : Array Char := Id.run do
  let n := src.size
  let at2 (i : Nat) (a b : Char) : Bool := i + 1 < n && src[i]! == a && src[i + 1]! == b
  let mut out : Array Char := Array.mkEmpty n
  let mut i := 0
  while i < n do
    if at2 i '/' '-' then
      -- the closing `-/` at or after `i + 2`
      let mut j := i + 2
      let mut close : Option Nat := none
      while j + 1 < n && close.isNone do
        if at2 j '-' '/' then close := some j else j := j + 1
      match close with
      | some c => i := c + 2
      | none => out := out.push src[i]!; i := i + 1
    else
      out := out.push src[i]!
      i := i + 1
  return out

def isModChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.'

/-- The imports Python's `re.findall` finds with
`^\s*(?:K\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)` under `re.M`, where `K`
ranges over `keywords` and, with `atLeastOne`, the `(?:…)*` is a `+`. The
keywords and `import` share no prefix, so the regex never backtracks into
them and a deterministic scan is exact. -/
def findImports (src : Array Char) (keywords : List String) (atLeastOne : Bool) : Array String :=
  Id.run do
    let n := src.size
    let lit (i : Nat) (w : String) : Bool := Id.run do
      let cs := w.toList
      if i + cs.length > n then return false
      let mut k := i
      for c in cs do
        if src[k]! != c then return false
        k := k + 1
      return true
    let spaces (i : Nat) : Nat := Id.run do
      let mut j := i
      while j < n && isPySpace src[j]! do j := j + 1
      return j
    -- `w\s+` at `i`: the index after the blanks
    let word (i : Nat) (w : String) : Option Nat :=
      if lit i w then
        let j := spaces (i + w.length)
        if j > i + w.length then some j else none
      else none
    let ident (i : Nat) : Nat := Id.run do
      let mut j := i
      while j < n && isModChar src[j]! do j := j + 1
      return j
    -- one match attempt at a line start; the end of the match and its name
    let attempt (p : Nat) : Option (Nat × String) := Id.run do
      let mut i := spaces p
      let mut count := 0
      let mut more := true
      while more do
        match keywords.findSome? (word i ·) with
        | some j => i := j; count := count + 1
        | none => more := false
      if atLeastOne && count == 0 then return none
      let some k := word i "import" | return none
      -- `(?:all\s+)?`, falling back to reading `all` as the name
      if let some j := word k "all" then
        let e := ident j
        if e > j then return some (e, String.ofList (src.extract j e).toList)
      let e := ident k
      if e > k then return some (e, String.ofList (src.extract k e).toList) else return none
    -- `^` under `re.M`: position 0 and every position after a newline; a
    -- search resumes at the first line start at or after a match's end
    let mut found := #[]
    let mut p := 0
    let mut more := true
    while more do
      let mut from_ := p
      if let some (e, name) := attempt p then
        found := found.push name
        from_ := e
      let mut j := from_
      while j < n && src[j]! != '\n' do j := j + 1
      if j < n then p := j + 1 else more := false
    return found

/-! ## The classification -/

def theoryPrefixes : List String :=
  ["Ix.Kernel.Verify.", "Ix.Kernel.SetTheory.", "Ix.Kernel.Model.", "Ix.Kernel.SetModel.",
   "Ix.Kernel.Semantics.", "Ix.Kernel.Term."]

/-- The lanes, by path: the model lane, the capstone assembly, and the base
(the rest). -/
def lane (path : String) : String :=
  if isCapstone path then "caps" else if isModelLane path then "model" else "base"

/-- The kernel imports only itself and the toolchain. -/
def boundary : List String := ["Init", "Std", "Lean"]

def rulesExempt : List String := ["Ix.Kernel.Model.Rules.Recompose"]

/-- The pure implementation the rules tier may not import. -/
def implMod (b : String) : Bool :=
  ["Ix.Kernel.Core", "Ix.Kernel.TypeChecker", "Ix.Kernel.CoreIO", "Ix.Kernel.DeclCheck",
   "Ix.Kernel.Cached"].contains b ||
  b.startsWith "Ix.Kernel.Checker" || b.startsWith "Ix.Kernel.Cached."

/-- The implementation modules the rules tier's elaboration closure reaches
today. A new door is a regression; a door no longer reached is progress:
delete it here and say so in the evidence note. -/
def rulesClosureDoors : List String :=
  ["Ix.Kernel.Core", "Ix.Kernel.TypeChecker", "Ix.Kernel.CoreIO", "Ix.Kernel.Checker",
   "Ix.Kernel.CheckerBase"]

/-- An insertion-ordered map, for the closure's first-entry parents (the
witnessing chains are those Python's dict order gives). -/
structure Parents where
  keys : Array String := #[]
  parent : Std.HashMap String String := {}

def Parents.insert (p : Parents) (k v : String) : Parents :=
  { keys := p.keys.push k, parent := p.parent.insert k v }

/-- The elaboration environment of `m`, and for each member the edge it
entered through (first hop: any non-meta import; later hops: public
imports only). -/
def closureWithParents (dir pub : Std.HashMap String (Array String)) (m : String) : Parents :=
  Id.run do
    let mut par : Parents := {}
    let mut todo : Array String := #[]
    for x in dir.getD m #[] do
      unless par.parent.contains x do
        par := par.insert x m
        todo := todo.push x
    while !todo.isEmpty do
      let x := todo.back!
      todo := todo.pop
      for y in pub.getD x #[] do
        unless par.parent.contains y do
          par := par.insert y x
          todo := todo.push y
    return par

def chainTo (par : Parents) (m t : String) : String := Id.run do
  let mut ch := #[t]
  let mut cur := t
  -- each step follows a parent edge towards `m`; the closure has finitely many
  for _ in [0:par.keys.size + 1] do
    if cur == m then break
    cur := par.parent.getD cur m
    ch := ch.push cur
  return " <- ".intercalate ch.toList

def pairLt (a b : String × String) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def run (args : List String) : IO UInt32 := do
  let (tree, unclassified) ← covered
  if ← reportUnclassified "LAYERING" unclassified then return 1
  if tree.isEmpty then
    IO.println "layering: no kernel modules under Ix/Kernel/; nothing to check"
    return 0
  let modName (rel : String) : String :=
    (String.ofList (rel.toList.take (rel.length - 5))).replace "/" "."
  let mods : Array String := tree.map modName
  let modSet : Std.HashSet String := Std.HashSet.ofArray mods
  let mut path : Std.HashMap String String := {}
  let mut imports : Std.HashMap String (Array String) := {}
  let mut pub : Std.HashMap String (Array String) := {}
  let mut dir : Std.HashMap String (Array String) := {}
  for rel in tree do
    let name := modName rel
    let src := stripBlockComments (← readText rel).toList.toArray
    path := path.insert name rel
    imports := imports.insert name (findImports src ["public", "private", "meta"] false)
    pub := pub.insert name ((findImports src ["public"] true).filter modSet.contains)
    dir := dir.insert name ((findImports src ["public", "private"] false).filter modSet.contains)
  let pathOf (m : String) := path.getD m ""
  let laneOf (m : String) := lane (pathOf m)
  let edges (m : String) := (imports.getD m #[]).filter modSet.contains
  let pairs (keep : String → String → Bool) (targets : String → Array String) :
      Array (String × String) :=
    (mods.foldl (fun acc a => acc ++ ((targets a).filter (keep a)).map (a, ·)) #[]).qsort pairLt
  let basev := pairs (fun a b => laneOf a == "base" && laneOf b == "model") edges
  let implv := pairs (fun a b => part? (pathOf a) == some .checker && theoryPrefixes.any (fun d => b.startsWith d))
    edges
  let boundv := pairs (fun _ b => !modSet.contains b && !boundary.contains ((b.splitOn ".").headD ""))
    (imports.getD · #[])
  let isRules (a : String) := isRulesTier (pathOf a) && !rulesExempt.contains a
  let rulesv := pairs (fun a b => isRules a && implMod b) edges
  let rulesMods := (mods.filter isRules).qsort (· < ·)
  let closures : Std.HashMap String Parents :=
    rulesMods.foldl (fun acc m => acc.insert m (closureWithParents dir pub m)) {}
  -- the first rules module (in order) to reach each door, with its chain
  let mut doorsSeen : Array (String × String × String) := #[]
  for m in rulesMods do
    let par := closures.getD m {}
    for t in par.keys do
      if implMod t && !doorsSeen.any (·.1 == t) then
        doorsSeen := doorsSeen.push (t, m, chainTo par m t)
  let doorsSorted := doorsSeen.qsort (fun a b => a.1 < b.1)
  let newDoors := (doorsSorted.filter (!rulesClosureDoors.contains ·.1))
  -- the closure clause waits for the rules tier: while the subtree is
  -- imported step by step there may be no rules module yet
  let goneDoors := if rulesMods.isEmpty then #[] else
    (rulesClosureDoors.toArray.filter (fun t => !doorsSeen.any (·.1 == t))).qsort (· < ·)
  if args.contains "--list" then
    for (a, b) in basev do IO.println s!"{a} -> {b}"
    for m in rulesMods do
      let par := closures.getD m {}
      let marks := " ".intercalate ((par.keys.qsort (· < ·)).toList.map fun x =>
        (if implMod x then "!" else "") ++ x)
      IO.println s!"closure {m} ({par.keys.size}): {marks}"
    for (t, _, ch) in doorsSorted do IO.println s!"door {t}: {ch}"
    return 0
  let mut fail := false
  let report (title : String) (items : Array (String × String)) (hint : String) : IO Bool := do
    if items.isEmpty then return false
    IO.println s!"LAYERING FAIL — {title} ({items.size}):"
    for (a, b) in items do IO.println s!"    {a} -> {b}"
    IO.println s!"    {hint}"
    return true
  fail := (← report "base module importing the model lane" basev
    "the checker and Ix/Kernel/{Verify,SetTheory,Term,SetModel,Semantics}/* stand BELOW the lane; \
    nothing there may import Ix/Kernel/Model/*.") || fail
  fail := (← report "implementation importing theory" implv
    "the checker (Tests/Ix/Kernel/KernelLayout.lean) must never import \
    Ix/Kernel/{SetTheory,SetModel,Semantics,Model,Verify,Term}/*.") || fail
  fail := (← report "rules tier importing the pure implementation" rulesv
    "Ix/Kernel/Rules/* and Ix/Kernel/Model/Rules/* are stated over Ix/Kernel/CoreDefs and may not \
    import Ix/Kernel/{Core,TypeChecker,CoreIO,Checker*,DeclCheck} or Cached/*.") || fail
  fail := (← report "rules tier CLOSURE reaching an unlisted implementation module"
    (newDoors.map (fun (t, m, _) => (m, t)) ++ newDoors.map (fun (_, _, ch) => ("  via", ch)))
    "a new public re-export carries the impl into the rules tier's elaboration environment; \
    repoint it (see --list).") || fail
  fail := (← report "rules tier CLOSURE door no longer reached (record the progress)"
    (goneDoors.map ("rulesClosureDoors", ·))
    "delete the door from rulesClosureDoors in Tests/Ix/Kernel/Layering.lean and say so in the \
    evidence note.") || fail
  fail := (← report "kernel importing outside itself and the toolchain" boundv
    "the checker and the theory import only themselves, Init, Std and Lean; Ix's boundary \
    imports the kernel, never the reverse.") || fail
  if fail then return 1
  let count (l : String) := (mods.filter (laneOf · == l)).size
  let doors := if rulesMods.isEmpty then " (no rules module yet)" else " as listed"
  let checker := (mods.filter fun m => part? (pathOf m) == some .checker).size
  IO.println s!"layering: base {count "base"} / model {count "model"} / caps {count "caps"} modules \
    ({checker} of the checker); {basev.size} base->model edges, {implv.size} impl->theory, \
    {rulesv.size} rules->impl, {boundv.size} outside the boundary; rules closure: \
    {rulesMods.size} modules, {doorsSeen.size} doors{doors}"
  return 0

end Tests.Ix.Kernel.Layering

def main (args : List String) : IO UInt32 := Tests.Ix.Kernel.Layering.run args
