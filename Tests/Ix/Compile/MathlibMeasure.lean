/-
  mathlib-measure: the switch-on library measurement (plan M1, "Then the
  measurement"). Untrusted measurement tooling; it changes no compiler code
  and asserts nothing about meaning.

  Three phases, selected by `M1G_PHASE`, all on the library file
  `M1G_FILE` (default `Benchmarks/Compile/CompileMathlib.lean`), writing
  into `M1G_DIR` (default `out/m1g`):

  * `compile`: compile the file's environment as `ix compile-lean` does,
    Pass 3 (the only mode), `M1G_WORKERS` workers (default 32);
    write the output (`M1G_OUT`, if set) and the compile's own records:
    `failures.tsv` (every block failure, the block rule's refusals marked),
    `cliques.tsv` (every definition clique of the input, as the compiler
    planned it: outcome, encoding, cause, members, carried lemmas,
    canonical constants), `p3blocks.tsv`, `p3heads.tsv` (the changed
    inductive blocks and their image-kind auxiliaries).
  * `classify`: read `ixe-diff`'s rows (`M1G_DIFF_TSV`) and its `--names`
    listing (`M1G_DIFF_OUT`, the `+`/`-` lines) and classify every moved,
    added and removed name against the records of `compile` and the input's
    reference graph; write `classes.tsv` and the kernel name set
    `kernel-names.txt` (every moved or added name and every dependent of
    one, as present in the switch-on output).
  * `kernels`: `Tests.Ix.Compile.Pass3.kernelRun` in anonymous mode on
    `kernel-names.txt` over `M1G_OUT` (the certified checker on the whole
    file, `check-rs --anon --skip-deps`, `check-lean --anon`, every failure
    read from the fail-out files), with per-leg coverage asserted (the
    certified checker: every name has a verdict; the anonymous legs: every
    distinct address checked); writes
    `kernel-failures.tsv` and keeps the checkers' outputs under
    `M1G_DIR/kernels/`.

  Run: `M1G_PHASE=<phase> … .lake/build/bin/IxTests --ignored mathlib-measure`.
-/
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.Pass3Cliques

open Lean

namespace Tests.Ix.Compile.MathlibMeasure

abbrev IxName := _root_.Ix.Name

/-- The list separator inside one TSV field (names may contain `,` or `|`). -/
def sep : String := "\x1f"

def clean (s : String) : String := (s.replace "\n" " ").replace "\t" " "

def px (n : IxName) : String := n.pretty

def joinNames (ns : Array IxName) : String := sep.intercalate (ns.map px).toList

def splitNames (s : String) : Array String :=
  if s.isEmpty then #[] else (s.splitOn sep).toArray

def env (k d : String) : IO String := return (← IO.getEnv k).getD d

def writeLines (p : System.FilePath) (header : String) (rows : Array String) : IO Unit :=
  IO.FS.writeFile p (header ++ "\n" ++ String.join (rows.toList.map (· ++ "\n")))

def readRows (p : System.FilePath) : IO (Array (Array String)) := do
  let ls := (← IO.FS.readFile p).splitOn "\n"
  return (ls.drop 1).toArray.filterMap fun l =>
    if l.isEmpty then none else some (l.splitOn "\t").toArray

/-! ## compile -/

/-- The why of a non-transported outcome with the clique's own names
replaced, for tallying. -/
def normWhy (all : Array IxName) (why : String) : String :=
  let w := all.foldl (fun w m => w.replace (px m) "<m>") why
  (w.take 110).toString

def runCompile (dir : System.FilePath) : IO UInt32 := do
  let path ← env "M1G_FILE" "Benchmarks/Compile/CompileMathlib.lean"
  let workers := ((← IO.getEnv "M1G_WORKERS").bind (·.toNat?)).getD 32
  let fe ← getFileEnvCore path
  let constList ← Ix.EnvScope.defaultConstList fe path
  IO.println s!"[m1g] {path}: {constList.length} constants, {workers} workers"
  let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv fe.env constList).mapError toString)
  let t0 ← IO.monoMsNow
  let on ← match ← Ix.CompileM.compileLeanInput input (numWorkers := workers) (dbg := true) with
    | .ok o => pure o
    | .error e => throw (IO.userError s!"compile failed: {e}")
  IO.println s!"[m1g] switch on: {on.bytes.size} B, {on.blockCount} blocks, \
    {on.ungroundedCount} ungrounded, {on.cenv.ungrounded.size} block failures, {(← IO.monoMsNow) - t0} ms"
  if let some out := ← IO.getEnv "M1G_OUT" then
    IO.FS.writeBinFile out on.bytes
    IO.println s!"[m1g] wrote {out}"
  -- every block failure, in full
  let fails := on.cenv.ungrounded.toArray.qsort (fun a b => a.1.pretty < b.1.pretty)
  let refused := fails.filter fun (_, e) => (e.splitOn "caller refused").length > 1
  writeLines (dir / "failures.tsv") "name\trefused\tmessage" <| fails.map fun (n, e) =>
    s!"{px n}\t{decide ((e.splitOn "caller refused").length > 1)}\t{clean e}"
  IO.println s!"[m1g] block failures: {fails.size}; callers refused (block rule): {refused.size}"
  for (n, e) in fails do
    IO.println s!"[m1g]   failure: {px n}: {(clean e).take 400}"
  -- the changed inductive blocks (Pass 3 images)
  writeLines (dir / "p3blocks.tsv") "key\tall" <| on.cenv.p3Blocks.toArray.map fun (k, all) =>
    s!"{px k}\t{joinNames all}"
  writeLines (dir / "p3heads.tsv") "head\tkey" <| on.cenv.p3Heads.toArray.map fun (h, k) =>
    s!"{px h}\t{px k}"
  IO.println s!"[m1g] changed inductive blocks: {on.cenv.p3Blocks.size}, image-kind heads: {on.cenv.p3Heads.size}"
  -- every definition clique, as the compiler planned it
  let cenv := on.cenv
  let const? := cenv.env.get?
  let cliques := Tests.Ix.Compile.Pass3Cliques.leanCliques constList
  let mut rows : Array String := #[]
  let mut tally : Std.HashMap String (Nat × Array String) := {}
  let mut transported := 0
  for cl in cliques do
    let all := cl.map _root_.Ix.Name.fromLeanName
    let some n := all[0]? | continue
    let (kind, enc, cause, carried, canon, detail) : String × String × String × Array IxName × Array IxName × String :=
      match cenv.p3Cliques.get? n with
      | none => ("notInTable", "-", "-", #[], #[], "no encoding marker, or members in one block")
      | some (_, carried) =>
        match Ix.Compile.Pass.planClique const? (Ix.Compile.Pass.cliqueAddr cenv) all carried with
        | .notEncoded why => ("notEncoded", "-", "-", carried, #[], why)
        | .unchanged enc src => ("unchanged", enc.tag, s!"order by {src.tag}", carried, #[], "")
        | .baseline enc c why => ("baseline", enc.tag, c, carried, #[], why)
        | .transported p =>
          ("TRANSPORTED", p.encoding.tag, if p.causes.isEmpty then "-" else "causes", carried,
           p.canon.map (·.1.name), p.record)
    if kind == "TRANSPORTED" then transported := transported + 1
    rows := rows.push s!"{kind}\t{enc}\t{cause}\t{joinNames all}\t{joinNames carried}\t{joinNames canon}\t{clean detail}"
    let key := if kind == "TRANSPORTED" then s!"{kind} {enc}" else s!"{kind} {enc} {cause}: {normWhy all detail}"
    let (k, ex) := tally.getD key (0, #[])
    tally := tally.insert key (k + 1, if ex.size < 3 then ex.push (px n) else ex)
  writeLines (dir / "cliques.tsv") "kind\tencoding\tcause\tmembers\tcarried\tcanonical\tdetail" rows
  IO.println s!"[m1g] definition cliques of two or more members: {cliques.size}; transported {transported}; \
    clique table entries {(cenv.p3Cliques.toList.filter fun (n, (all, _)) => all[0]? == some n).length}"
  for (key, (k, ex)) in tally.toArray.qsort (fun a b => a.2.1 > b.2.1) do
    IO.println s!"[m1g]   {k}  {key}  e.g. {ex}"
  return 0

/-! ## classify -/

/-- The reverse reference graph of the input (an inductive owns its
constructors, as in `Tests.Ix.Compile.Pass3.cone`). -/
def reverseRefs (consts : List (Name × ConstantInfo)) : Std.HashMap Name (Array Name) := Id.run do
  -- `alter` keeps each array unshared, so a push does not copy it (a library
  -- constant like `Eq` has hundreds of thousands of dependents)
  let add (rev : Std.HashMap Name (Array Name)) (r n : Name) : Std.HashMap Name (Array Name) :=
    rev.alter r fun | none => some #[n] | some a => some (a.push n)
  let mut rev : Std.HashMap Name (Array Name) := {}
  for (n, ci) in consts do
    for r in ci.getUsedConstantsAsSet do
      rev := add rev r n
    match ci with
    | .ctorInfo cv => rev := add rev cv.induct n
    | _ => pure ()
  return rev

def coneOf (rev : Std.HashMap Name (Array Name)) (seeds : Array Name) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  let mut todo := seeds
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if out.contains n then continue
    out := out.insert n
    for d in rev.getD n #[] do
      if !out.contains d then todo := todo.push d
  return out

/-- Whether a proper or improper prefix of `n` is in `s`. -/
def underAny (s : Std.HashSet Name) : Name → Bool
  | .anonymous => false
  | n@(.str p _) => s.contains n || underAny s p
  | n@(.num p _) => s.contains n || underAny s p

def lastStr : Name → String
  | .str _ s => s
  | .num p _ => lastStr p
  | .anonymous => ""

def isEqLemma (n : Name) : Bool :=
  let s := lastStr n
  s == "eq_def" || s == "eq_unfold" || (s.startsWith "eq_" && (s.drop 3).toString.all Char.isDigit)

def bump (m : Std.HashMap String (Nat × Array String)) (k ex : String) : Std.HashMap String (Nat × Array String) :=
  let (c, xs) := m.getD k (0, #[])
  m.insert k (c + 1, if xs.size < 3 then xs.push ex else xs)

def printTally (title : String) (m : Std.HashMap String (Nat × Array String)) : IO Unit := do
  IO.println s!"[m1g] {title}: {m.fold (fun a _ v => a + v.1) 0}"
  for (k, (c, ex)) in m.toArray.qsort (fun a b => a.2.1 > b.2.1) do
    IO.println s!"[m1g]   {c}  {k}  e.g. {ex}"

def runClassify (dir : System.FilePath) : IO UInt32 := do
  let path ← env "M1G_FILE" "Benchmarks/Compile/CompileMathlib.lean"
  let fe ← getFileEnvCore path
  let consts ← Ix.EnvScope.defaultConstList fe path
  let byPretty : Std.HashMap String Name := consts.foldl
    (fun m (n, _) => m.insert (_root_.Ix.Name.fromLeanName n).pretty n) {}
  IO.println s!"[m1g] {path}: {consts.length} constants, {byPretty.size} distinct pretty names"
  let resolve (s : String) : Option Name := byPretty.get? s
  -- the compile's records
  let cliques ← readRows (dir / "cliques.tsv")
  let mut members : Std.HashSet Name := {}
  let mut carried : Std.HashSet Name := {}
  let mut canonStr : Std.HashSet String := {}
  let mut keptMembers : Std.HashSet Name := {}
  for r in cliques do
    let ms := (splitNames r[3]!).filterMap resolve
    if r[0]! == "TRANSPORTED" then
      members := ms.foldl (·.insert ·) members
      carried := ((splitNames r[4]!).filterMap resolve).foldl (·.insert ·) carried
      canonStr := (splitNames r[5]!).foldl (·.insert ·) canonStr
    else keptMembers := ms.foldl (·.insert ·) keptMembers
  let blockRows ← readRows (dir / "p3blocks.tsv")
  let blockMembers : Std.HashSet Name := blockRows.foldl (fun s r =>
    ((splitNames r[1]!).filterMap resolve).foldl (·.insert ·) s) {}
  let heads : Std.HashSet Name := (← readRows (dir / "p3heads.tsv")).foldl (fun s r =>
    match resolve r[0]! with | some n => s.insert n | none => s) {}
  let failed : Std.HashSet String := (← readRows (dir / "failures.tsv")).foldl (fun s r => s.insert r[0]!) {}
  IO.println s!"[m1g] records: {members.size} transported members, {carried.size} carried lemmas, \
    {canonStr.size} canonical constants; {blockMembers.size} members of changed inductive blocks, \
    {heads.size} image-kind heads; {failed.size} block failures"
  -- the units and cones
  let rev := reverseRefs consts
  let cliqueUnit : Array Name := consts.toArray.filterMap fun (n, _) =>
    if underAny members n then some n else none
  let imageUnit : Array Name := consts.toArray.filterMap fun (n, _) =>
    if underAny blockMembers n || heads.contains n then some n else none
  let cliqueCone := coneOf rev cliqueUnit
  let imageCone := coneOf rev imageUnit
  IO.println s!"[m1g] clique units {cliqueUnit.size} names, cone {cliqueCone.size}; \
    image units {imageUnit.size} names, cone {imageCone.size}"
  -- the diff
  let diff ← readRows (System.FilePath.mk (← env "M1G_DIFF_TSV" (dir / "diff.tsv").toString))
  let diffOut ← IO.FS.readFile (← env "M1G_DIFF_OUT" (dir / "diff.out").toString)
  let added := (diffOut.splitOn "\n").toArray.filterMap fun l =>
    if l.startsWith "  + " then some (l.drop 4).toString else none
  let removed := (diffOut.splitOn "\n").toArray.filterMap fun l =>
    if l.startsWith "  - " then some (l.drop 4).toString else none
  let classOf (n : Name) : String :=
    if members.contains n then "clique:member"
    else if carried.contains n then "clique:carried-lemma"
    else if underAny members n then
      (if isEqLemma n then "clique:unit-eq-lemma (LAZY)" else "clique:unit-other")
    else if heads.contains n then "image:head (Lean aux name denoting an image)"
    else if blockMembers.contains n then "image:block-member"
    else if underAny blockMembers n then "image:unit-other"
    else if cliqueCone.contains n && imageCone.contains n then "cone:both"
    else if cliqueCone.contains n then "cone:clique"
    else if imageCone.contains n then "cone:image"
    else "UNEXPLAINED"
  let mut rows : Array String := #[]
  let mut tally : Std.HashMap String (Nat × Array String) := {}
  let mut byCause : Std.HashMap String (Nat × Array String) := {}
  let mut moved : Array Name := #[]
  let mut unresolved : Array String := #[]
  for r in diff do
    let s := r[0]!
    let cause := r[2]!
    let mut cls := "UNRESOLVED (not an input name)"
    match resolve s with
    | some n =>
      moved := moved.push n
      cls := classOf n
    | none => unresolved := unresolved.push s
    rows := rows.push s!"moved\t{s}\t{cause}\t{cls}"
    tally := bump tally cls s
    byCause := bump byCause s!"{cls} / {cause}" s
  let mut addTally : Std.HashMap String (Nat × Array String) := {}
  for s in added do
    let cls := if canonStr.contains s then "added:clique-canonical"
      else if (s.splitOn "._ix").length > 1 || s.endsWith "._ix" then "added:_ix-other"
      else if (resolve s).isSome then "added:input-name (absent from the reference)"
      else "added:UNEXPLAINED"
    rows := rows.push s!"added\t{s}\t-\t{cls}"
    addTally := bump addTally cls s
  let mut remTally : Std.HashMap String (Nat × Array String) := {}
  for s in removed do
    let cls := if failed.contains s then "removed:block-failure"
      else match resolve s with
        | some n => s!"removed:{classOf n}"
        | none => "removed:not-an-input-name"
    rows := rows.push s!"removed\t{s}\t-\t{cls}"
    remTally := bump remTally cls s
  writeLines (dir / "classes.tsv") "change\tname\tdiff_cause\tclass" rows
  IO.println s!"[m1g] diff: {diff.size} moved, {added.size} added, {removed.size} removed; \
    {unresolved.size} moved names not resolved to an input name: {unresolved.toList.take 10}"
  printTally "moved names by class" tally
  printTally "moved names by class / ixe-diff cause" byCause
  printTally "added names by class" addTally
  printTally "removed names by class" remTally
  -- LAZY: the equation lemmas of transported members, moved or not
  let eqs := consts.toArray.filterMap fun (n, _) =>
    if underAny members n && isEqLemma n then some n else none
  let movedSet : Std.HashSet Name := moved.foldl (·.insert ·) {}
  let eqMoved := eqs.filter movedSet.contains
  IO.println s!"[m1g] equation lemmas of transported members: {eqs.size}; moved {eqMoved.size} \
    (of which carried {(eqMoved.filter carried.contains).size}); unmoved {eqs.size - eqMoved.size}"
  for n in eqMoved do
    IO.println s!"[m1g]   moved eq lemma: {(_root_.Ix.Name.fromLeanName n).pretty}{if carried.contains n then " (carried)" else ""}"
  -- the kernel name set: every moved or added name and every dependent of one
  let deps := coneOf rev moved
  let mut kset : Std.HashSet String := {}
  let mut depsOnly := 0
  let mut depTally : Std.HashMap String (Nat × Array String) := {}
  let mut depRows : Array String := #[]
  for n in deps do
    let s := (_root_.Ix.Name.fromLeanName n).pretty
    if failed.contains s then continue
    unless movedSet.contains n do
      depsOnly := depsOnly + 1
      -- which moved names it references directly
      let refs := match fe.env.find? n with
        | some ci => ci.getUsedConstantsAsSet.toArray.filter movedSet.contains
        | none => #[]
      let refCls := (refs.map classOf).toList.eraseDups
      let cls := s!"{classOf n} / references {refCls}"
      depTally := bump depTally cls s
      depRows := depRows.push s!"{s}\t{cls}\t{sep.intercalate (refs.map fun r => (_root_.Ix.Name.fromLeanName r).pretty).toList}"
    kset := kset.insert s
  writeLines (dir / "deps-unmoved.tsv") "name\tclass\tmoved_refs" depRows
  printTally "dependents of a moved name that did not move (class / classes of the moved names referenced directly)" depTally
  for s in added do kset := kset.insert s
  let names := kset.toArray.qsort (· < ·)
  IO.FS.writeFile (dir / "kernel-names.txt") (String.join (names.toList.map (· ++ "\n")))
  IO.println s!"[m1g] kernel names: {names.size} (moved {moved.size}, added {added.size}, \
    dependents of a moved name that did not move themselves {depsOnly})"
  return if unresolved.isEmpty then 0 else 1

/-! ## kernels -/

def runKernels (dir : System.FilePath) : IO UInt32 := do
  let some out := ← IO.getEnv "M1G_OUT" | throw (IO.userError "M1G_OUT unset")
  let names := ((← IO.FS.readFile (dir / "kernel-names.txt")).splitOn "\n").toArray.filter (!·.isEmpty)
  let kdir := dir / "kernels"
  IO.FS.createDirAll kdir
  -- the distinct anonymous addresses among the names (what check-lean --anon checks)
  let parts ← IO.ofExcept (Ixon.deEnvVerifiedLazy (← IO.FS.readBinFile out))
  let names ← IO.ofExcept (Tests.Ix.Compile.Pass3.expandKernelTargets parts names)
  let addrOf : Std.HashMap String String := parts.namedRows.foldl
    (fun m row => m.insert row.name.pretty (toString row.addr)) {}
  let addrs : Std.HashSet String := names.foldl (fun s n => match addrOf.get? n with
    | some a => s.insert a | none => s) {}
  IO.println s!"[m1g] kernels: {names.size} names, {addrs.size} distinct addresses"
  let t0 ← IO.monoMsNow
  let r ← Tests.Ix.Compile.Pass3.kernelRun kdir (System.FilePath.mk out) names (anon := true) (skipDeps := true)
  IO.println s!"[m1g] kernels done in {(← IO.monoMsNow) - t0} ms; checked {r.checked}; {r.failed.size} failure(s)"
  writeLines (dir / "kernel-failures.tsv") "leg\tname\tmessage" <| r.failed.map fun (l, n, m) =>
    s!"{l}\t{n}\t{clean m}"
  for (l, n, m) in r.failed do
    IO.println s!"[m1g]   {l}: {n}: {(clean m).take 300}"
  -- coverage per leg: the certified checker every name (its verdict rows are
  -- looked up per name), check-rs and check-lean every distinct address
  -- (anonymous mode checks an address once, whatever names share it)
  let mut ok := true
  for (leg, k) in r.checked do
    let want := if leg == "cert" then names.size else addrs.size
    let line := s!"{leg} checked {k}, requested {want}"
    if k == want then IO.println s!"[m1g] coverage ok: {line}"
    else
      ok := false
      IO.println s!"[m1g] COVERAGE FAIL: {line}"
  return if ok && r.failed.isEmpty then 0 else 1

def run : IO UInt32 := do
  let dir := System.FilePath.mk (← env "M1G_DIR" "out/m1g")
  IO.FS.createDirAll dir
  match ← env "M1G_PHASE" "" with
  | "compile" => runCompile dir
  | "classify" => runClassify dir
  | "kernels" => runKernels dir
  -- unset: a measurement, not a gate; an ignored sweep skips it
  | "" => IO.println "[m1g] M1G_PHASE unset: nothing measured (compile | classify | kernels)"; return 0
  | p => IO.eprintln s!"[m1g] unknown M1G_PHASE '{p}' (compile | classify | kernels)"; return 2

end Tests.Ix.Compile.MathlibMeasure
