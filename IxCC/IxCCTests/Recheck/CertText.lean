import IxCC.Cli
import IxCCTests.Corpus.Manifest

/-! # `tests-cert-text`: a certificate `compile` writes is one `check-cert` accepts

`ixcc compile` writes the producer's certificate file text, which the producer has read back
through the verifier's reader (`Cert.readBack`, `RcReplay.Cert.readBack`), and it runs
`check-cert`'s verifier (`Cli.checkText`: that reader with every text and decode limit, Stage A,
the replay) on that text before it writes anything. Two parts:

* **every root** of every committed corpus manifest (the nine registered families and `k1`,
  `ownership`, `phase2-arity`), of `fixtures/rc/budget` and of `fixtures/rc/deep`, under `--rc off`,
  `on` and `auto`: what `compile` computes (`Cli.compileText`) either declines, so nothing is
  written, or gives the text it writes; `check-cert`'s verifier, run again on that text, accepts it
  and gives the same object;
* **the depth limit** (`fixtures/rc/deep`): `deep240`'s plain-RC certificate nests 726 deep, past
  the certificate text's 512, so `ixcc compile --rc on` declines with the limit's reason and writes
  no object and no certificate, and `--rc auto` falls back to the immortal policy naming that
  reason and writes a certificate `check-cert` accepts; `deep168`'s nests 510 and compiles under
  every mode, and `check-cert` accepts each certificate written, through the command line. -/

set_option autoImplicit false

namespace IxCCTests.Recheck.CertText

open IxCC IxCC.Recheck System Lean

def fail (r : IO.Ref Nat) (msg : String) : IO Unit := do
  r.modify (· + 1)
  IO.eprintln s!"FAIL {msg}"

def expect (r : IO.Ref Nat) (ok : Bool) (msg : String) : IO Unit := unless ok do fail r msg

/-- Every committed corpus manifest: the registered families and the unregistered ones. -/
def manifests : List FilePath :=
  IxCCTests.Corpus.families ++
    (["fixtures/ixon-v4/k1/corpus.json", "fixtures/ownership/corpus.json",
      "fixtures/corpus/phase2-arity/corpus.json"] : List FilePath)

/-- The RC inputs outside the manifests, by directory and roots. -/
def rcInputs : List (FilePath × List String) :=
  [("fixtures/rc/budget", ["IxCCTests.Own.Budget.fanUnder", "IxCCTests.Own.Budget.fanOver"]),
   ("fixtures/rc/deep", ["IxCCTests.Cert.Deep.deep240", "IxCCTests.Cert.Deep.deep168"])]

/-- One compile's input: a closure, its sidecar and the roots, as `ixcc compile` takes them. -/
structure Case where
  label : String
  closure : FilePath
  equations : FilePath
  roots : List String

def cases : IO (Array Case) := do
  let mut out := #[]
  for path in manifests do
    let m ← IxCCTests.Corpus.Family.read path
    let dir : FilePath := m.directory
    for f in m.fixtures do
      for r in f.roots do
        out := out.push { label := s!"{m.family}/{f.name}/{r.name}", closure := dir / f.closure.path
                          equations := dir / f.equations.path, roots := r.name :: r.together }
  for (dir, roots) in rcInputs do
    for root in roots do
      out := out.push { label := s!"{dir}/{root}", closure := dir / "anonymous.ixe"
                        equations := dir / "consumer.equations.json", roots := [root] }
  return out

/-- Ingress as `ixcc compile` runs it (`Cli.readInputs`, then `Recheck.ingress`). -/
def ingressOf (c : Case) : IO (Except Err Input) := do
  let bytes ← IO.FS.readBinFile c.closure
  let text ← IO.FS.readFile c.equations
  match Src.Hints.checkJsonText text >>= fun () => Json.parse text with
  | .error e => return .error { stage := .ingress, code := "hints", message := s!"{c.equations}: {e}" }
  | .ok json => return ingress bytes json c.roots

def modes : List (String × Cli.RcMode) := [("off", .off), ("on", .on), ("auto", .auto)]

/-- Counts: compiles, the certificates written and accepted again, declines. -/
structure Counts where
  roots : Nat := 0
  compiled : Nat := 0
  declined : Nat := 0
  ingressDeclined : Nat := 0

/-- **Every root**, under every mode: what `compile` writes, `check-cert` accepts. -/
def everyRoot (r : IO.Ref Nat) : IO Counts := do
  let mut n : Counts := {}
  for c in ← cases do
    n := { n with roots := n.roots + 1 }
    match ← ingressOf c with
    | .error _ => n := { n with ingressDeclined := n.ingressDeclined + 1 }
    | .ok inp =>
      let cfg := Config.forInput {} inp
      match checkFnParams cfg.names inp.program with
      | .error _ => n := { n with declined := n.declined + modes.length }
      | .ok () =>
        for (name, mode) in modes do
          match Cli.compileText mode cfg inp with
          | .error _ => n := { n with declined := n.declined + 1 }
          | .ok (text, _, a) =>
            n := { n with compiled := n.compiled + 1 }
            match Cli.checkText cfg inp text with
            | .ok (_, a') =>
              expect r (a'.object == a.object)
                s!"{c.label} --rc {name}: check-cert's verifier gives another object from the text compile writes"
            | .error e =>
              fail r s!"{c.label} --rc {name}: check-cert refuses the text compile writes: {e.render}"
  return n

/-- `ixcc` in process: the exit code. -/
def ixcc (args : List String) : IO UInt32 := IxCC.Cli.main args

/-- **The depth limit**, through the command line (in process) and `Cli`'s pure functions. -/
def depthLimit (r : IO.Ref Nat) (work : FilePath) : IO (Array String) := do
  let dir : FilePath := "fixtures/rc/deep"
  let base := [(dir / "anonymous.ixe").toString, "--equations", (dir / "consumer.equations.json").toString]
  let mut out := #[]
  let reason := "JSON nesting depth 726 exceeds maximum 512"
  -- deep240 under --rc on: declined with the limit's reason, nothing written
  let obj := work / "deep240.on.o"
  let cert := work / "deep240.on.cert"
  let code ← ixcc (["compile"] ++ base ++ ["--root", "IxCCTests.Cert.Deep.deep240", "--rc", "on",
    "-o", obj.toString, "--emit-cert", cert.toString])
  expect r (code == 1) s!"deep240 --rc on: exit {code}, expected 1"
  expect r (!(← obj.pathExists) && !(← cert.pathExists)) "deep240 --rc on: an object or a certificate was written"
  let case240 : Case := { label := "deep240", closure := dir / "anonymous.ixe"
                          equations := dir / "consumer.equations.json", roots := ["IxCCTests.Cert.Deep.deep240"] }
  let .ok inp ← ingressOf case240 | do fail r "deep240: ingress refused"; return out
  let cfg := Config.forInput {} inp
  match Cli.compileText .on cfg inp with
  | .ok _ => fail r "deep240 --rc on: compiled"
  | .error e =>
    expect r (e.stage == .cert && e.code == "cert.parse" && e.message == reason)
      s!"deep240 --rc on: declined for another reason: {e.render}"
  out := out.push s!"deep240 --rc on: declined (exit 1, cert: cert.parse: {reason}), no object, no certificate"
  -- deep240 under --rc auto: the immortal fallback, naming the reason; its certificate accepted
  match Cli.produceText .auto cfg inp with
  | .ok (_, _, policy, _) =>
    expect r (policy == some s!"immortal (plain RC refused: cert: cert.parse: {reason})")
      s!"deep240 --rc auto: policy {policy}"
  | .error e => fail r s!"deep240 --rc auto: declined: {e.render}"
  let rows : List (String × String × String) :=
    [("deep240", "auto", "immortal"), ("deep240", "off", "zero RC"),
     ("deep168", "on", "plain RC"), ("deep168", "auto", "plain RC"), ("deep168", "off", "zero RC")]
  for (root, mode, what) in rows do
    let obj := work / s!"{root}.{mode}.o"
    let cert := work / s!"{root}.{mode}.cert"
    let rootArgs := ["--root", s!"IxCCTests.Cert.Deep.{root}"]
    let code ← ixcc (["compile"] ++ base ++ rootArgs ++ ["--rc", mode, "-o", obj.toString,
      "--emit-cert", cert.toString])
    expect r (code == 0) s!"{root} --rc {mode}: compile exit {code}"
    if code != 0 then continue
    let text ← IO.FS.readFile cert
    let depth := (Src.Hints.scanJson text).maxDepth
    let want := if root == "deep168" && mode != "off" then 510 else 8
    expect r (depth == want) s!"{root} --rc {mode}: the certificate nests {depth}, expected {want}"
    let code ← ixcc (["check-cert"] ++ base ++ rootArgs ++ ["--cert", cert.toString])
    expect r (code == 0) s!"{root} --rc {mode}: check-cert exit {code} on the certificate compile wrote"
    out := out.push s!"{root} --rc {mode}: {what}, certificate nesting {depth}, check-cert accepts it"
  return out

def run : IO UInt32 := do
  let r ← IO.mkRef 0
  IO.println "tests-cert-text"
  let lines ← IO.FS.withTempDir fun work => depthLimit r work
  for l in lines do IO.println s!"  {l}"
  let t0 ← IO.monoMsNow
  let n ← everyRoot r
  IO.println s!"  every root: {n.roots} roots × {modes.length} modes; {n.compiled} compiles, each \
    certificate written accepted again by check-cert's verifier with the same object; {n.declined} \
    declined, {n.ingressDeclined} roots declined at ingress ({(← IO.monoMsNow) - t0} ms)"
  let failures ← r.get
  if failures == 0 then
    IO.println "tests-cert-text: ok"
    return 0
  else
    IO.println s!"tests-cert-text: {failures} failures"
    return 1

end IxCCTests.Recheck.CertText
