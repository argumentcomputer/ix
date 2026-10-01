import CompilatrixTests.Corpus.Manifest
import CompilatrixTests.Support.Rng
import Compilatrix.Tools.Census
import Compilatrix.Tools.SourceScan
import Compilatrix.Recheck.Produce

/-! The corpus builder (MT.1): `lake exe corpus`.

* **`rebuild`** (manual; needs ix and Lean): for each fixture of a family,
  compile the anonymous closure of its roots and the named twin with the
  pinned ix (`ix compile --equations`), check that their equation lists
  agree, resolve every root, definition and equation name to its content
  address with `ix addr-of` against the twin, write the address-resolved
  sidecar (`compilatrix/k1-equations/1`) and the admission census, draw the
  generated cases from their seeds, run every case through Lean 4.34's
  interpreter (`lean --run`), check the independent constants, and rewrite
  the manifest's derived fields. It refuses an ix binary whose SHA-256 is not
  the manifest's. This replaces `plans/x86-phase1/bench-k1/build.sh`, whose
  commands it runs (byte-identical output on the five K1 closures).
* **`check`** (offline; no ix, no Lean unless `--interpret`): verify every
  frozen file against the manifest (hashes and sizes, the sidecar's roots,
  addresses and counts, the census reproduced byte for byte from the
  closure), re-ingress every root, regenerate the generated arguments from
  their seeds, check each case's shape and constants, and scan the sources
  for forbidden constructs. With `--interpret`, also re-run the interpreter
  and compare its output with the recorded values. -/

namespace CompilatrixTests.Corpus

open Lean System Compilatrix.Tools.Check
open CompilatrixTests.Support (RngM Rng)

structure Tools where
  ix : Option FilePath := none
  /-- Directories prepended to `PATH` for ix (it asks `lake env` for
  `LEAN_PATH` and `lean` for the sysroot). -/
  ixPath : List String := []
  lean : String := "lean"
  work : FilePath := "plans/corpus/work"

/-- Run a process; its exit code, standard output and standard error. -/
def proc (cmd : String) (args : Array String) (cwd : Option FilePath := none)
    (path : List String := []) (stdin : Option String := none) : IO (UInt32 × String × String) := do
  let env ← if path.isEmpty then pure #[] else do
    let old := (← IO.getEnv "PATH").getD ""
    pure #[("PATH", some (":".intercalate (path ++ [old])))]
  let child ← IO.Process.spawn { cmd, args, cwd, env, stdin := .piped, stdout := .piped, stderr := .piped }
  let (input, child) ← child.takeStdin
  if let some s := stdin then input.putStr s
  input.flush
  let outTask ← IO.asTask child.stdout.readToEnd .dedicated
  let err ← child.stderr.readToEnd
  let out ← IO.ofExcept outTask.get
  let code ← child.wait
  return (code, out, err)

def mustRun (label cmd : String) (args : Array String) (cwd : Option FilePath := none)
    (path : List String := []) (stdin : Option String := none) (log : Option FilePath := none) :
    IO String := do
  let (code, out, err) ← proc cmd args cwd path stdin
  if let some l := log then IO.FS.writeFile l (out ++ err)
  unless code == 0 do
    throw (IO.userError s!"{label}: `{cmd} {" ".intercalate args.toList}` exited {code}\n{String.ofList (err.toList.reverse.take 2000).reverse}")
  return out

/-! ## Cases -/

/-- The arguments a root's generator draws. -/
def Gen.draw (g : Gen) : List (List Nat) :=
  let draw : RngM (List (List Nat)) := (List.range g.count).mapM fun _ =>
    g.ranges.mapM fun (lo, hi) => RngM.range lo hi
  (draw.run (Rng.ofSeed (UInt64.ofNat g.seed))).1

/-- The hand-written cases, then the generated ones (values to be filled). -/
def Root.withGenerated (r : Root) : Root :=
  let hand := r.cases.filter (!·.generated)
  let gen := match r.gen with
    | some g => g.draw.map fun args =>
        let old := r.cases.find? fun c => c.generated && c.args == args
        { args, generated := true, value := (old.map (·.value)).getD "" }
    | none => []
  { r with cases := hand ++ gen }

/-- Whether the interpreter runs a case: not when an argument has no word
(the compiled root must return status 3 before it runs, and the source
program may not terminate in reasonable time on such an argument). -/
def Case.interpreted (c : Case) : Bool := !c.args.any (· ≥ limit)

/-- The value recorded for a case the interpreter does not run. -/
def noWord : String := "-"

/-- The interpreter's output on every case of a fixture, in order (`noWord`
for the cases it does not run). -/
def interpret (t : Tools) (m : Family) (f : Fixture) (work : FilePath) : IO (List (List String)) := do
  let cwd : FilePath := m.sourceRoot
  if f.protocol == "args" then
    f.roots.mapM fun r => r.cases.mapM fun c => do
      if !c.interpreted then return noWord
      let out ← mustRun s!"{f.name} {r.name} {c.args}" t.lean
        (#["-Dlinter.all=false", "--run", f.source.path] ++ (c.args.map toString).toArray) (some cwd)
      let v := out.trimAscii.toString
      need (!v.contains (Char.ofNat 10)) s!"{f.name} {r.name} {c.args}: the interpreter printed more than one line:\n{out}"
      return v
  else
    let lines := f.roots.flatMap fun r => (r.cases.filter (·.interpreted)).map fun c =>
      " ".intercalate (r.name :: c.args.map toString)
    let input := String.join (lines.map (· ++ "\n"))
    IO.FS.writeFile (work / s!"{f.name}.cases.txt") input
    let out ← mustRun s!"{f.name}: lean --run" t.lean #["-Dlinter.all=false", "--run", f.source.path] (some cwd) (stdin := some input)
    IO.FS.writeFile (work / s!"{f.name}.lean-run.txt") out
    let outs := (out.splitOn "\n").filter (!·.isEmpty)
    unless outs.length == lines.length do
      throw (IO.userError s!"{f.name}: the interpreter printed {outs.length} lines for {lines.length} cases")
    let mut rest := outs
    let mut acc := #[]
    for r in f.roots do
      let mut vs := #[]
      for c in r.cases do
        if c.interpreted then
          vs := vs.push (rest.headD "")
          rest := rest.drop 1
        else vs := vs.push noWord
      acc := acc.push vs.toList
    return acc.toList

/-- Fill the cases' values from the interpreter and check the constants. -/
def fillValues (f : Fixture) (outs : List (List String)) : IO Fixture := do
  let roots ← (f.roots.zip outs).mapM fun (r, vs) => do
    let cases ← (r.cases.zip vs).mapM fun (c, v) => do
      if let some k := c.constant then
        need (k == v) s!"{f.name} {r.name} {c.args}: the interpreter printed {v}, the constant is {k}"
      return { c with value := v }
    return { r with cases }
  return { f with roots }

/-! ## Rebuild -/

/-- An ix command line from its template. -/
def fill (template : List String) (subst : List (String × String)) : Array String :=
  (template.drop 1).toArray.map fun a => ((subst.find? (·.1 == a)).map (·.2)).getD a

/-- Write `content` to `path` unless it is already there; whether it changed. -/
def writeIfChanged (path : FilePath) (content : ByteArray) : IO Bool := do
  if ← path.pathExists then
    if (← IO.FS.readBinFile path) == content then return false
  IO.FS.writeBinFile path content
  return true

def fileRec (dir : FilePath) (path : String) (bytes : Bool := false) : IO FileRec := do
  let p := dir / path
  return { path, sha256 := ← sha256 p, bytes := ← (if bytes then do pure (some (← IO.FS.readBinFile p).size) else pure none) }

/-- The census of a closure, as the `census` tool writes it. -/
def censusText (ixe : ByteArray) (equations : Json) : IO String := do
  return (Compilatrix.Tools.Census.report ixe (← Compilatrix.Tools.Census.names equations)).pretty ++ "\n"

def rebuildFixture (t : Tools) (m : Family) (f : Fixture) (log : IO.Ref (Array String)) : IO Fixture := do
  let some ix := t.ix | throw (IO.userError "rebuild needs --ix PATH")
  let ix ← IO.FS.realPath ix
  let work ← IO.FS.realPath t.work
  let dir : FilePath := m.directory
  let cwd : FilePath := m.sourceRoot
  let src := f.source.path
  let consts := ",".intercalate f.consts
  let anonIxe := work / s!"{f.name}.ixe"
  let anonEqs := work / s!"{f.name}.anon.equations.json"
  let namedIxe := work / s!"{f.name}.named.ixe"
  let namedEqs := work / s!"{f.name}.named.equations.json"
  let subst := [("{consts}", consts), ("{ixe}", anonIxe.toString), ("{equations}", anonEqs.toString),
    ("{named}", namedIxe.toString), ("{named-equations}", namedEqs.toString), ("{src}", src)]
  let _ ← mustRun s!"{f.name}: ix compile --anon" ix.toString (fill anonCommand subst) (some cwd) t.ixPath
    (log := some (work / s!"{f.name}.anon.log"))
  let _ ← mustRun s!"{f.name}: ix compile (named)" ix.toString (fill namedCommand subst) (some cwd) t.ixPath
    (log := some (work / s!"{f.name}.named.log"))
  let anon ← readJson anonEqs
  let named ← readJson namedEqs
  need (anon == named) s!"{f.name}: the anonymous and named closures' equation lists differ"
  -- every root, definition and equation name, resolved against the named twin
  let pairs ← arrField named "equations"
  let mut names := f.consts
  for p in pairs do
    names := names ++ [← strField p "definition", ← strField p "equation"]
  names := names.eraseDups.mergeSort (· ≤ ·)
  let mut addr : List (String × String) := []
  for n in names do
    let out ← mustRun s!"{f.name}: ix addr-of {n}" ix.toString (fill addrCommand (subst ++ [("{name}", n)]))
      (some cwd) t.ixPath
    let a := ((out.splitOn "\n").filter (!·.trimAscii.isEmpty)).getLast?.getD "" |>.trimAscii.toString
    need (isHex 64 a) s!"{f.name}: ix addr-of {n} printed {out}"
    addr := addr ++ [(n, a)]
  let lookup := fun (n : String) => ((addr.find? (·.1 == n)).map (·.2)).getD ""
  let failures ← checked (OJson.ofJson ((named.getObjVal? "failures").toOption.getD (.arr #[])))
  let sidecar : OJson := .obj #[("format", .str "compilatrix/k1-equations/1"), ("source", .str src),
    ("roots", .arr (f.consts.map fun n => OJson.obj #[("name", .str n), ("address", .str (lookup n))]).toArray),
    ("equations", .arr (← pairs.mapM fun p => do
      let d ← strField p "definition"
      let e ← strField p "equation"
      return OJson.obj #[("definition", .str d), ("definition_address", .str (lookup d)),
        ("equation", .str e), ("equation_address", .str (lookup e))])),
    ("failures", failures)]
  IO.FS.createDirAll dir
  let eqText := sidecar.render
  let ixeBytes ← IO.FS.readBinFile anonIxe
  let census ← censusText ixeBytes (← checked (Json.parse eqText))
  let changed := [(f.closure.path, ← writeIfChanged (dir / f.closure.path) ixeBytes),
    (f.equations.path, ← writeIfChanged (dir / f.equations.path) eqText.toUTF8),
    (f.census.path, ← writeIfChanged (dir / f.census.path) census.toUTF8)]
  for (p, c) in changed do
    log.modify (·.push s!"  {dir / p}: {if c then "CHANGED" else "unchanged"}")
  -- cases: regenerate, then interpret
  let f := { f with roots := f.roots.map fun r => { r.withGenerated with address := lookup r.name } }
  let f ← fillValues f (← interpret t m f work)
  return { f with
    source := { f.source with sha256 := ← sha256 (cwd / src) }
    closure := ← fileRec dir f.closure.path (bytes := true)
    equations := ← fileRec dir f.equations.path
    equationCount := pairs.size
    failureCount := (← arrField named "failures").size
    namedEnvSha256 := ← sha256 namedIxe
    census := ← fileRec dir f.census.path }

def rebuild (t : Tools) (manifest : FilePath) (only : List String) : IO Unit := do
  let m ← Family.read manifest
  let some ix := t.ix | throw (IO.userError "rebuild needs --ix PATH")
  let digest ← sha256 ix
  need (digest == m.producer.ixBinarySha256)
    s!"{ix}: SHA-256 {digest}, but the manifest pins {m.producer.ixBinarySha256} (ix {m.producer.ixRevision})"
  IO.FS.createDirAll t.work
  let log ← IO.mkRef #[]
  let mut fixtures := []
  for f in m.fixtures do
    if !only.isEmpty && !only.contains f.name then
      fixtures := fixtures ++ [f]
      continue
    let (f', ms) ← timedIO (rebuildFixture t m f log)
    IO.println s!"{m.family}/{f.name}: {f'.closure.bytes.getD 0} bytes, {f'.equationCount} equations, \
      {f'.roots.length} roots, {(f'.roots.map (·.cases.length)).foldl (· + ·) 0} cases ({ms} ms)"
    for l in ← log.get do IO.println l
    log.set #[]
    fixtures := fixtures ++ [f']
  let m' := { m with fixtures }
  let old ← IO.FS.readFile manifest
  let text := m'.toOJson.render
  if old == text then IO.println s!"{manifest}: unchanged"
  else
    IO.FS.writeFile manifest text
    IO.println s!"{manifest}: rewritten"
where
  timedIO {α} (x : IO α) : IO (α × Nat) := do
    let t0 ← IO.monoMsNow
    let r ← x
    return (r, (← IO.monoMsNow) - t0)

/-! ## Check -/

/-- Words the Phase 1 sources must not use (as `benchmarks/fixtures/Check.lean`). -/
def forbidden : List String := ["partial", "unsafe", "implemented_by", "extrinsicFix", "Task"]

def scanSource (path : FilePath) : IO Unit := do
  let tokens ← checked ((Compilatrix.Tools.SourceScan.scan (← IO.FS.readFile path)).mapError (s!"{path}: " ++ ·))
  for tok in tokens do
    if tok.kind == .name && (forbidden.contains tok.text || (tok.text.splitOn ".").any forbidden.contains) then
      throw (IO.userError s!"{path}:{tok.line}: forbidden construct {tok.text}")

structure CheckStats where
  fixtures : Nat := 0
  roots : Nat := 0
  cases : Nat := 0
  declines : Nat := 0
  files : Nat := 0

def checkFixture (t : Tools) (interpretToo : Bool) (m : Family) (f : Fixture) (st : CheckStats) :
    IO CheckStats := do
  let dir : FilePath := m.directory
  let label := s!"{m.family}/{f.name}"
  let src : FilePath := (m.sourceRoot : FilePath) / f.source.path
  need ((← sha256 src) == f.source.sha256) s!"{label}: {src} changed since the closure was built"
  scanSource src
  need (!f.source.license.isEmpty && !f.source.variant.isEmpty) s!"{label}: no licence or variant"
  let ixe ← IO.FS.readBinFile (dir / f.closure.path)
  need ((← sha256 (dir / f.closure.path)) == f.closure.sha256 && some ixe.size == f.closure.bytes)
    s!"{label}: {f.closure.path} differs from the manifest"
  need ((← sha256 (dir / f.equations.path)) == f.equations.sha256) s!"{label}: {f.equations.path} differs"
  need ((← sha256 (dir / f.census.path)) == f.census.sha256) s!"{label}: {f.census.path} differs"
  let eqs ← readJson (dir / f.equations.path)
  need ((← strField eqs "format") == "compilatrix/k1-equations/1") s!"{label}: sidecar format"
  need ((← strField eqs "source") == f.source.path) s!"{label}: the sidecar names another source"
  need ((← arrField eqs "equations").size == f.equationCount && (← arrField eqs "failures").size == f.failureCount)
    s!"{label}: equation or failure count differs"
  let sideRoots ← (← arrField eqs "roots").toList.mapM fun r => return (← strField r "name", ← strField r "address")
  need (sideRoots.map (·.1) == f.consts) s!"{label}: the sidecar's roots are not the consts"
  -- the census, reproduced byte for byte
  let census ← censusText ixe eqs
  need (census == (← IO.FS.readFile (dir / f.census.path))) s!"{label}: the census does not reproduce"
  let eqsJson ← IO.FS.readFile (dir / f.equations.path)
  let eqsParsed ← checked (Json.parse eqsJson)
  let mut st := { st with fixtures := st.fixtures + 1, files := st.files + 3 }
  for r in f.roots do
    need ((sideRoots.find? (·.1 == r.name)).map (·.2) == some r.address)
      s!"{label} {r.name}: address {r.address} is not the sidecar's"
    need (["nat", "bool"].contains r.result) s!"{label} {r.name}: result {r.result}"
    -- ingress finds the root (no typing: the census covers it)
    match Compilatrix.Recheck.ingress ixe eqsParsed [r.name] (typecheck := false) with
    | .ok _ => pure ()
    | .error e => throw (IO.userError s!"{label} {r.name}: ingress: {e.render}")
    if let some g := r.gen then
      need (g.ranges.length == r.params) s!"{label} {r.name}: generator ranges"
      need ((r.cases.filter (·.generated)).map (·.args) == g.draw)
        s!"{label} {r.name}: the generated arguments are not the seed's"
    for c in r.cases do
      need (c.args.length == r.params) s!"{label} {r.name} {c.args}: {r.params} parameters"
      need (!c.value.isEmpty) s!"{label} {r.name} {c.args}: no interpreter value"
      need ((c.expect r).isSome) s!"{label} {r.name} {c.args}: value {c.value} is not a {r.result}"
      if let some k := c.constant then
        need (k == c.value) s!"{label} {r.name} {c.args}: value {c.value}, constant {k}"
    st := { st with roots := st.roots + 1, cases := st.cases + r.cases.length
                    declines := st.declines + (if r.decline.isSome then 1 else 0) }
  if interpretToo then
    let work ← IO.FS.realPath t.work
    let outs ← interpret t m f work
    for (r, vs) in f.roots.zip outs do
      for (c, v) in r.cases.zip vs do
        need (c.value == v) s!"{label} {r.name} {c.args}: recorded {c.value}, the interpreter prints {v}"
  return st

def check (t : Tools) (manifests : List FilePath) (interpretToo : Bool) : IO Unit := do
  if interpretToo then IO.FS.createDirAll t.work
  let mut total : CheckStats := {}
  for path in manifests do
    let m ← Family.read path
    -- the manifest is in its canonical form (what a rebuild writes)
    need ((← IO.FS.readFile path) == m.toOJson.render) s!"{path}: not in canonical form (rebuild rewrites it)"
    need (m.producer.ixBinarySha256.length == 64 && m.producer.ixRevision.length == 40)
      s!"{path}: producer pins"
    let before := total
    for f in m.fixtures do
      total ← checkFixture t interpretToo m f total
    IO.println s!"{path}: {m.family} ({m.tier}): {total.fixtures - before.fixtures} closures, \
      {total.roots - before.roots} roots ({total.declines - before.declines} expected declines), \
      {total.cases - before.cases} cases{if interpretToo then ", interpreter agrees" else ""}"
  IO.println s!"corpus check: {manifests.length} families, {total.fixtures} closures, {total.files} files, \
    {total.roots} roots, {total.cases} cases ok"

/-! ## Command line -/

def usage : String :=
  "usage: corpus check [MANIFEST…] [--interpret] [--lean LEAN] [--work DIR]\n" ++
  "       corpus rebuild MANIFEST --ix IX [--ix-path DIR]… [--lean LEAN] [--work DIR] [--only FIXTURE]…"

def main (args : List String) : IO UInt32 := cli "corpus" do
  let rec parse (t : Tools) (pos : List String) (only : List String) (interp : Bool) :
      List String → Except String (Tools × List String × List String × Bool)
    | [] => .ok (t, pos, only, interp)
    | "--ix" :: p :: rest => parse { t with ix := some p } pos only interp rest
    | "--ix-path" :: p :: rest => parse { t with ixPath := t.ixPath ++ [p] } pos only interp rest
    | "--lean" :: p :: rest => parse { t with lean := p } pos only interp rest
    | "--work" :: p :: rest => parse { t with work := p } pos only interp rest
    | "--only" :: n :: rest => parse t pos (only ++ [n]) interp rest
    | "--interpret" :: rest => parse t pos only true rest
    | a :: rest => if a.startsWith "--" then .error s!"unknown option {a}\n{usage}" else parse t (pos ++ [a]) only interp rest
  match args with
  | "check" :: rest =>
    let (t, pos, _, interp) ← checked (parse {} [] [] false rest)
    check t (if pos.isEmpty then families else pos.map FilePath.mk) interp
  | "rebuild" :: rest =>
    let (t, pos, only, _) ← checked (parse {} [] [] false rest)
    match pos with
    | [manifest] => rebuild t manifest only
    | _ => throw (IO.userError usage)
  | _ => throw (IO.userError usage)

end CompilatrixTests.Corpus
