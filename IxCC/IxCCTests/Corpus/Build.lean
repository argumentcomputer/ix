import IxCCTests.Corpus.Manifest
import IxCCTests.Support.Rng
import IxCC.Tools.Census
import IxCC.Tools.SourceScan
import IxCC.Recheck.Produce

/-! The corpus builder: `lake exe corpus`.

* **`rebuild`** (manual; needs ix and Lean): for each fixture of a family,
  compile the anonymous closure of its roots and the named twin with the
  pinned ix (`ix compile --equations`), check that their equation lists
  agree, resolve every root, definition and equation name to its content
  address with `ix addr-of` against the twin, write the address-resolved
  sidecar (`ixcc/k1-equations/1`) and the admission census, draw the
  generated cases from their seeds, run every case through Lean 4.34's
  interpreter (`lean --run`), check the independent constants, and rewrite
  the manifest's derived fields. It refuses an ix binary whose SHA-256 is not
  the manifest's. This replaces an earlier shell script, whose
  commands it runs (byte-identical output on the five K1 closures).
* **`check`** (offline; no ix, no Lean unless `--interpret`): verify every
  frozen file against the manifest (hashes and sizes, the sidecar's roots,
  addresses and counts, the census reproduced byte for byte from the
  closure), re-ingress every root, regenerate the generated arguments from
  their seeds, check each case's shape and constants, and scan the sources
  for forbidden constructs. With `--interpret`, also re-run the interpreter
  and compare its output with the recorded values. -/

namespace IxCCTests.Corpus

open Lean System IxCC.Tools.Check
open IxCCTests.Support (RngM Rng)

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
  let out ← IO.Process.output { cmd, args, cwd, env } stdin
  return (out.exitCode, out.stdout, out.stderr)

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
program may not terminate in reasonable time on such an argument), and not
on a `trap` case (no well-typed argument reaches a trap; the driver passes
a word where the source has no value). -/
def Case.interpreted (c : Case) : Bool := !c.args.any (· ≥ limit) && c.fail != some "trap" && !c.leanFails

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
    -- a fixture with no case to interpret (its roots declined, or Lean cannot
    -- run them) needs no interpreter run
    if lines.isEmpty then return f.roots.map fun r => r.cases.map fun _ => noWord
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
      if c.leanFails then
        let some k := c.constant | throw (IO.userError s!"{f.name} {r.name} {c.args}: `lean_fails` needs a constant")
        return { c with value := k }
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

/-- A fresh output directory retained with its diagnostic logs. `createDir`
refuses an existing path, so a command cannot reuse files from an earlier run. -/
def freshWorkDir (base : FilePath) : IO FilePath := do
  IO.FS.createDirAll base
  let base ← IO.FS.realPath base
  let work := base / s!"run-{← IO.monoNanosNow}"
  IO.FS.createDir work
  return work

/-- The census of a closure, as the `census` tool writes it. -/
def censusText (ixe : ByteArray) (equations : Json) : IO String := do
  return (IxCC.Tools.Census.report ixe (← IxCC.Tools.Census.names equations)).pretty ++ "\n"

/-- Validate structural resource metadata against the entire authenticated
closure, independently of roots and expected compiler declines. -/
def checkResourceClosure (ixe : ByteArray) (eqs : Json) : IO Unit := do
  let context ← checked (IxCC.Src.Hints.resourceOfJson eqs)
  if context.isSome then
    let env ← checked (IxCC.Ixon.V3.decodeAnonymousEnv ixe)
    let p ← checked (IxCC.Src.Ingress.ofEnv env #[])
    let p := { p with known := IxCC.Src.Pinned.known p, resource := context }
    checked (IxCC.Src.Resource.validate p)

/-- Bytes from lowercase hexadecimal (an even number of digits). -/
def hexBytes (s : String) : Option ByteArray := do
  let digit := fun (c : Char) =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let rec go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | h :: l :: rest, acc => do go rest (acc.push (UInt8.ofNat (16 * (← digit h) + (← digit l))))
    | [_], _ => none
  go s.toList .empty

/-- Parse the complete successful `ix check-equations` output protocol.
An empty pair list still requires the claim header and final count. Unknown,
truncated or duplicate pair lines are errors, rather than discarded output. -/
def verifiedPairs (out profile : String) : Except String (List CheckedPair) := do
  unless isHex 64 profile do throw "check-equations: malformed expected profile"
  let lines := (out.splitOn "\n").filter (!·.trimAscii.isEmpty)
  let header :: rest := lines | throw "check-equations: missing claim header"
  match words header with
  | ["check-equations:", "resource", "claim", "(root", root, "profile", bound, "holds"] =>
    let address := (root.dropEnd 1).toString
    unless isHex 64 address && root == address ++ "," && bound == profile ++ ")" do
      throw "check-equations: malformed root or different profile in claim header"
  | _ => throw "check-equations: malformed claim header"
  let footer :: reversed := rest.reverse | throw "check-equations: missing completion count"
  let count ← match words footer with
    | ["check-equations:", n, "checked", "pair(s)", "verified"] =>
      match n.toNat? with
      | some n => pure n
      | none => throw "check-equations: malformed completion count"
    | _ => throw "check-equations: malformed completion count"
  let mut pairs : List CheckedPair := []
  for line in reversed.reverse do
    let pair ← match words line with
      | [d, da, "↦", e, ea] =>
        if isHex 64 da && isHex 64 ea then
          pure ({ definition := d, definitionAddress := da, equation := e, equationAddress := ea } : CheckedPair)
        else throw "check-equations: malformed pair address"
      | _ => throw "check-equations: malformed pair line"
    unless !(pairs.any (·.definitionAddress == pair.definitionAddress)) do
      throw "check-equations: duplicate definition binding"
    pairs := pairs ++ [pair]
  unless count == pairs.length do throw "check-equations: completion count differs from pairs"
  return pairs

/-- Run `ix check-equations` on an annotated closure and its sidecar
(`args`), and record its verdict and the pairs it verified, which must be
exactly the sidecar's `resourceChecked` (by name and address, in order). -/
def resourceOf (ix work : FilePath) (name profile : String) (checkedPairs : List Json)
    (args : Array String) (cwd : FilePath) (path : List String) : IO (Resource × Unit) := do
  let (code, out, err) ← proc ix.toString args (some cwd) path
  IO.FS.writeFile (work / s!"{name}.check-equations.log") (out ++ err)
  need (code == 0) s!"{name}: ix check-equations exited {code}; see {work / s!"{name}.check-equations.log"}"
  let listed ← checkedPairs.mapM fun q => do
    return ({ definition := ← strField q "definition", definitionAddress := ← strField q "definitionAddress"
              equation := ← strField q "equation", equationAddress := ← strField q "equationAddress" } : CheckedPair)
  let pairs ← checked (verifiedPairs out profile)
  need (pairs == listed) s!"{name}: ix check-equations verified other pairs than the sidecar lists:\n{out}"
  return ({ profile, checkEquations := "pass", pairs }, ())

def rebuildFixture (t : Tools) (m : Family) (f : Fixture) (log : IO.Ref (Array String)) : IO Fixture := do
  let some ix := t.ix | throw (IO.userError "rebuild needs --ix PATH")
  let ix ← IO.FS.realPath ix
  let work ← freshWorkDir t.work
  log.modify (·.push s!"  work: {work}")
  let dir : FilePath := m.directory
  let cwd : FilePath := m.sourceRoot
  let src := f.source.path
  let consts := ",".intercalate f.consts
  let anonIxe := work / s!"{f.name}.ixe"
  let anonEqs := work / s!"{f.name}.anon.equations.json"
  let namedIxe := work / s!"{f.name}.named.ixe"
  let namedEqs := work / s!"{f.name}.named.equations.json"
  let profile ← match m.producer.profile with
    | some p => do pure [("{profile}", (← IO.FS.realPath p.path).toString)]
    | none => pure []
  let subst := [("{consts}", consts), ("{ixe}", anonIxe.toString), ("{equations}", anonEqs.toString),
    ("{named}", namedIxe.toString), ("{named-equations}", namedEqs.toString), ("{src}", src)] ++ profile
  let _ ← mustRun s!"{f.name}: ix compile --anon" ix.toString (fill m.producer.anonymous subst) (some cwd) t.ixPath
    (log := some (work / s!"{f.name}.anon.log"))
  let _ ← mustRun s!"{f.name}: ix compile (named)" ix.toString (fill m.producer.named subst) (some cwd) t.ixPath
    (log := some (work / s!"{f.name}.named.log"))
  let anon ← readJson anonEqs
  let named ← readJson namedEqs
  need (anon == named) s!"{f.name}: the anonymous and named closures' equation lists differ"
  -- ix's resource admission (an annotated closure under the family's profile):
  -- the effective profile and the checked pairs, re-verified by `ix check-equations`
  let checkedPairs ← match named.getObjVal? "resourceChecked" with
    | .ok _ => (·.toList) <$> arrField named "resourceChecked"
    | .error _ => pure []
  need ((named.getObjVal? "resourceChecked").isOk == (named.getObjVal? "resourceProfile").isOk)
    s!"{f.name}: resourceChecked and resourceProfile must occur together"
  let admission : Option (Resource × Unit) ← match named.getObjVal? "resourceProfile" with
    | .ok rp => do
      let address ← strField rp "address"
      let r ← resourceOf ix work f.name address checkedPairs (fill checkEquationsCommand subst) cwd t.ixPath
      pure (some r)
    | .error _ => pure none
  need (m.producer.profile.isSome || admission.isNone)
    s!"{f.name}: ix ran resource admission, but the family pins no profile"
  -- every root, definition and equation name, resolved against the named twin
  let pairs ← arrField named "equations"
  let mut names := f.consts
  for p in pairs ++ checkedPairs.toArray do
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
  -- the resource record, when admission ran: the profile (address and
  -- canonical bytes) and every checked pair with its contracts
  let resourceKeys ← match admission, named.getObjVal? "resourceProfile" with
    | some (r, _), .ok rp => do
      let bytes ← strField rp "bytes"
      need (hexBytes bytes).isSome s!"{f.name}: resourceProfile.bytes is not hex"
      let checkedOut ← checkedPairs.mapM fun q => do
        let d ← strField q "definition"
        let e ← strField q "equation"
        let da ← strField q "definitionAddress"
        let ea ← strField q "equationAddress"
        need (da == lookup d && ea == lookup e)
          s!"{f.name}: resourceChecked {d} ↦ {e}: addresses differ from ix addr-of"
        need ((← strField q "profile") == r.profile) s!"{f.name}: resourceChecked {d}: another profile"
        let contracts ← (← arrField q "contracts").toList.mapM fun c => do
          return OJson.obj #[("position", .nat (← nat (← field c "position"))),
            ("binder", .str (← strField c "binder")), ("uses", .str (← strField c "uses")),
            ("owned", .str (← strField c "owned")), ("locality", .str (← strField c "locality"))]
        return OJson.obj #[("definition", .str d), ("definition_address", .str da),
          ("equation", .str e), ("equation_address", .str ea), ("profile", .str r.profile),
          ("contracts", .arr contracts.toArray)]
      pure [("resource_profile", OJson.obj #[("address", .str r.profile), ("bytes", .str bytes)]),
        ("resource_checked", OJson.arr checkedOut.toArray)]
    | _, _ => pure []
  let sidecar : OJson := .obj (#[("format", .str "ixcc/k1-equations/1"), ("source", .str src),
    ("roots", .arr (f.consts.map fun n => OJson.obj #[("name", .str n), ("address", .str (lookup n))]).toArray),
    ("equations", .arr (← pairs.mapM fun p => do
      let d ← strField p "definition"
      let e ← strField p "equation"
      return OJson.obj #[("definition", .str d), ("definition_address", .str (lookup d)),
        ("equation", .str e), ("equation_address", .str (lookup e))])),
    ("failures", failures)] ++ resourceKeys.toArray)
  IO.FS.createDirAll dir
  let eqText := sidecar.render
  let ixeBytes ← IO.FS.readBinFile anonIxe
  -- A census reports decoding failures as data. Refreezing must reject them.
  let _ ← checked (IxCC.Ixon.V3.decodeAnonymousEnv ixeBytes)
  checkResourceClosure ixeBytes (← checked (Json.parse eqText))
  let census ← censusText ixeBytes (← checked (Json.parse eqText))
  -- Finish the independent interpreter checks before publishing this fixture.
  let f := { f with roots := f.roots.map fun r => { r.withGenerated with address := lookup r.name } }
  let f ← fillValues f (← interpret t m f work)
  let sourceSha256 ← sha256 (cwd / src)
  let namedEnvSha256 ← sha256 namedIxe
  let failureCount := (← arrField named "failures").size
  let changed := [(f.closure.path, ← writeIfChanged (dir / f.closure.path) ixeBytes),
    (f.equations.path, ← writeIfChanged (dir / f.equations.path) eqText.toUTF8),
    (f.census.path, ← writeIfChanged (dir / f.census.path) census.toUTF8)]
  for (p, c) in changed do
    log.modify (·.push s!"  {dir / p}: {if c then "CHANGED" else "unchanged"}")
  return { f with
    source := { f.source with sha256 := sourceSha256 }
    closure := ← fileRec dir f.closure.path (bytes := true)
    equations := ← fileRec dir f.equations.path
    equationCount := pairs.size
    failureCount
    namedEnvSha256
    census := ← fileRec dir f.census.path
    resource := admission.map (·.1) }

def rebuild (t : Tools) (manifest : FilePath) (only : List String) : IO Unit := do
  let m ← Family.read manifest
  let some ix := t.ix | throw (IO.userError "rebuild needs --ix PATH")
  let digest ← sha256 ix
  need (digest == m.producer.ixBinarySha256)
    s!"{ix}: SHA-256 {digest}, but the manifest pins {m.producer.ixBinarySha256} (ix {m.producer.ixRevision})"
  let m ← match m.producer.profile with
    | some p => do pure { m with producer.profile := some { p with sha256 := ← sha256 p.path } }
    | none => pure m
  IO.FS.createDirAll t.work
  -- Stage the entire family. No fixture is replaced if a later producer or
  -- interpreter invocation fails. The manifest is published last.
  let stage ← freshWorkDir t.work
  let staged := { m with directory := stage.toString }
  let log ← IO.mkRef #[]
  let mut fixtures := []
  for f in m.fixtures do
    if !only.isEmpty && !only.contains f.name then
      fixtures := fixtures ++ [f]
      continue
    let (f', ms) ← timedIO (rebuildFixture t staged f log)
    IO.println s!"{m.family}/{f.name}: {f'.closure.bytes.getD 0} bytes, {f'.equationCount} equations, \
      {f'.roots.length} roots, {(f'.roots.map (·.cases.length)).foldl (· + ·) 0} cases ({ms} ms)"
    for l in ← log.get do IO.println l
    log.set #[]
    fixtures := fixtures ++ [f']
  let m' := { m with fixtures }
  let old ← IO.FS.readFile manifest
  let text := m'.toOJson.render
  IO.FS.createDirAll m.directory
  for f in fixtures do
    if !only.isEmpty && !only.contains f.name then continue
    for artifact in [f.closure, f.equations, f.census] do
      let target := (m.directory : FilePath) / artifact.path
      let changed ← writeIfChanged target (← IO.FS.readBinFile (stage / artifact.path))
      IO.println s!"  {target}: {if changed then "CHANGED" else "unchanged"}"
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

def scanSource (path : FilePath) (allowed : List String := []) : IO Unit := do
  let forbidden := forbidden.filter (!allowed.contains ·)
  let tokens ← checked ((IxCC.Tools.SourceScan.scan (← IO.FS.readFile path)).mapError (s!"{path}: " ++ ·))
  for tok in tokens do
    if tok.kind == .name && (forbidden.contains tok.text || (tok.text.splitOn ".").any forbidden.contains) then
      throw (IO.userError s!"{path}:{tok.line}: forbidden construct {tok.text}")

structure CheckStats where
  fixtures : Nat := 0
  roots : Nat := 0
  cases : Nat := 0
  declines : Nat := 0
  files : Nat := 0

/-- The resource record of a fixture against its sidecar (offline): the
manifest's profile address is the sidecar's `resource_profile.address`,
which is the BLAKE3 hash of the profile bytes it carries and the profile of
every checked pair; `ix check-equations` passed and verified exactly the
sidecar's checked pairs, each of which is among its unfolding equations. A
closure without a record carries no resource keys. -/
def checkResourceRecord (label : String) (m : Family) (f : Fixture) (eqs : Json) : IO Unit := do
  match f.resource, eqs.getObjVal? "resource_profile" with
  | none, .error _ =>
    need (eqs.getObjVal? "resource_checked" |>.toOption).isNone s!"{label}: checked pairs without a profile"
  | none, .ok _ => throw (IO.userError s!"{label}: the sidecar records a resource profile, the manifest none")
  | some _, .error _ => throw (IO.userError s!"{label}: the manifest records a resource profile, the sidecar none")
  | some r, .ok rp =>
    need m.producer.profile.isSome s!"{label}: a resource record in a family without a profile"
    need ((← strField rp "address") == r.profile && isHex 64 r.profile)
      s!"{label}: the manifest's profile address {r.profile} is not the sidecar's"
    let bytes ← present (hexBytes (← strField rp "bytes")) s!"{label}: resource_profile.bytes is not hex"
    need (toString (IxCC.Ixon.Address.blake3Pure bytes) == r.profile)
      s!"{label}: the profile bytes do not hash to {r.profile}"
    need (r.checkEquations == "pass") s!"{label}: ix check-equations failed on this closure"
    let listed ← (← arrField eqs "resource_checked").toList.mapM fun q => do
      need ((← strField q "profile") == r.profile) s!"{label}: a checked pair names another profile"
      return ({ definition := ← strField q "definition", definitionAddress := ← strField q "definition_address"
                equation := ← strField q "equation", equationAddress := ← strField q "equation_address" } : CheckedPair)
    need (listed == r.pairs) s!"{label}: the sidecar's checked pairs are not the verified ones"
    let eqns ← (← arrField eqs "equations").toList.mapM fun e => do
      return (← strField e "definition_address", ← strField e "equation_address")
    for q in listed do
      need (eqns.contains (q.definitionAddress, q.equationAddress))
        s!"{label}: checked pair {q.definition} ↦ {q.equation} is not among the sidecar's equations"

def checkFixture (t : Tools) (interpretToo : Bool) (m : Family) (f : Fixture) (st : CheckStats) :
    IO CheckStats := do
  let dir : FilePath := m.directory
  let label := s!"{m.family}/{f.name}"
  let src : FilePath := (m.sourceRoot : FilePath) / f.source.path
  need ((← sha256 src) == f.source.sha256) s!"{label}: {src} changed since the closure was built"
  need (f.allowConstructs.isEmpty || f.roots.all (·.decline.isSome))
    s!"{label}: `allow_constructs` is for fixtures whose roots are all declined"
  let sharedAllowed := (m.fixtures.filter fun g =>
    g.source.path == f.source.path && g.roots.all (·.decline.isSome)).flatMap (·.allowConstructs)
  scanSource src sharedAllowed
  need (!f.source.license.isEmpty && !f.source.variant.isEmpty) s!"{label}: no licence or variant"
  let ixe ← IO.FS.readBinFile (dir / f.closure.path)
  need ((← sha256 (dir / f.closure.path)) == f.closure.sha256 && some ixe.size == f.closure.bytes)
    s!"{label}: {f.closure.path} differs from the manifest"
  need ((← sha256 (dir / f.equations.path)) == f.equations.sha256) s!"{label}: {f.equations.path} differs"
  need ((← sha256 (dir / f.census.path)) == f.census.sha256) s!"{label}: {f.census.path} differs"
  let eqs ← readJson (dir / f.equations.path)
  need ((← strField eqs "format") == "ixcc/k1-equations/1") s!"{label}: sidecar format"
  need ((← strField eqs "source") == f.source.path) s!"{label}: the sidecar names another source"
  need ((← arrField eqs "equations").size == f.equationCount && (← arrField eqs "failures").size == f.failureCount)
    s!"{label}: equation or failure count differs"
  let sideRoots ← (← arrField eqs "roots").toList.mapM fun r => return (← strField r "name", ← strField r "address")
  need (sideRoots.map (·.1) == f.consts) s!"{label}: the sidecar's roots are not the consts"
  checkResourceRecord label m f eqs
  checkResourceClosure ixe eqs
  -- the census, reproduced byte for byte
  let census ← censusText ixe eqs
  need (census == (← IO.FS.readFile (dir / f.census.path))) s!"{label}: the census does not reproduce"
  let eqsJson ← IO.FS.readFile (dir / f.equations.path)
  let eqsParsed ← checked (Json.parse eqsJson)
  let mut st := { st with fixtures := st.fixtures + 1, files := st.files + 3 }
  for r in f.roots do
    need ((sideRoots.find? (·.1 == r.name)).map (·.2) == some r.address)
      s!"{label} {r.name}: address {r.address} is not the sidecar's"
    need (["nat", "bool", "enum", "other"].contains r.result) s!"{label} {r.name}: result {r.result}"
    need ((r.result == "enum") == r.ctors.isSome) s!"{label} {r.name}: `ctors` goes with an enum result"
    need (r.result != "other" || (r.decline.isSome && r.cases.isEmpty))
      s!"{label} {r.name}: an `other` result is a declined root without cases"
    need (r.together.all fun n => f.consts.contains n && n != r.name)
      s!"{label} {r.name}: `together` names other roots of the fixture"
    -- ingress finds the roots (no typing: the census covers it), or declines
    -- them as the manifest expects
    match IxCC.Recheck.ingress ixe eqsParsed (r.name :: r.together) (typecheck := false) with
    | .ok _ => pure ()
    | .error e =>
      -- a root the manifest expects declined at ingress
      unless r.decline == some { stage := e.stage.name, code := e.code } do
        throw (IO.userError s!"{label} {r.name}: ingress: {e.render}")
    if let some g := r.gen then
      need (g.ranges.length == r.params) s!"{label} {r.name}: generator ranges"
      need ((r.cases.filter (·.generated)).map (·.args) == g.draw)
        s!"{label} {r.name}: the generated arguments are not the seed's"
    for c in r.cases do
      need (c.args.length == r.params) s!"{label} {r.name} {c.args}: {r.params} parameters"
      need (!c.value.isEmpty) s!"{label} {r.name} {c.args}: no interpreter value"
      need ((c.expect r).isSome) s!"{label} {r.name} {c.args}: value {c.value} is not a {r.result}"
      need ((c.fail.toList ++ c.allow).all failures.contains) s!"{label} {r.name} {c.args}: unknown failure"
      need (!c.spurious || c.fail.isSome || !c.allow.isEmpty)
        s!"{label} {r.name} {c.args}: `spurious` qualifies a `fail` or an `allow`"
      need (c.stack.all fun s => s % 16 == 0 && s ≥ 8192)
        s!"{label} {r.name} {c.args}: the driver's stack is a multiple of 16 of at least 8 KiB"
      need (c.region.all (· > 0)) s!"{label} {r.name} {c.args}: an empty region"
      need (!c.leanFails || c.constant.isSome) s!"{label} {r.name} {c.args}: `lean_fails` needs a constant"
      if let some k := c.constant then
        need (k == c.value) s!"{label} {r.name} {c.args}: value {c.value}, constant {k}"
    st := { st with roots := st.roots + 1, cases := st.cases + r.cases.length
                    declines := st.declines + (if r.decline.isSome then 1 else 0) }
  if interpretToo then
    let work ← IO.FS.realPath t.work
    let outs ← interpret t m f work
    for (r, vs) in f.roots.zip outs do
      for (c, v) in r.cases.zip vs do
        need (!c.interpreted || c.value == v) s!"{label} {r.name} {c.args}: recorded {c.value}, the interpreter prints {v}"
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
    if let some p := m.producer.profile then
      need ((← sha256 p.path) == p.sha256) s!"{path}: the profile {p.path} differs from the manifest"
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

def toolMain (args : List String) : IO UInt32 := cli "corpus" do
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

end IxCCTests.Corpus
