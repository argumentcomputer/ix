import CompilatrixTests.Pipeline.Support
import CompilatrixTests.Rt.Differential
import CompilatrixTests.Rt.Cases
import CompilatrixTests.Lam.Differential

/-! The compiler (M1.I1): the `compilatrix` command line on the fixtures,
`produce` + `Recheck.run` against the stage suites' pipelines, the
certificate's serialisation, and the declines.

* **The command line** (`Compilatrix.Cli.main`, in process, or the built
  binary with `--bin`): each bench-k1 closure is compiled to an object with
  its certificate and signatures; `check-cert` accepts the certificate, and
  `compile --cert` with it writes the identical object (the recheck needs
  nothing from `produce`). `k1.ixe` is compiled with its five roots into
  one object exporting `cx_K1_fib` … `cx_K1_gcd`. With `--cc`, every
  object is linked with `fixtures/x86/runtime_driver.c` for each root and
  run at the manifest's test and bench sizes against `expected.txt` and
  `bench_expected`, reading the result back through the driver's decoder
  with the signature the compiler printed.
* **The same object**: `produce` then `run` makes byte for byte the object
  the stage suites' pipeline makes today (`Src.load`, `Lam.erase`,
  `Anf.Pipeline.produce`, `Cfg.ofAnf`, `Rt.lower`, `Select.run`,
  `Alloc.run`, `Backend.emit`; `CompilatrixTests.Rt.Machine.compile`).
* **Round trips**: the certificate's JSON parses back to a certificate with
  the same JSON, and `run` on it makes the same object.
* **Declines**: the fallback route (a sidecar without equations) is
  declined at `fir` with `fir.closures`; a root with six parameters with
  `rt.params` (without the check, stacking would reject its wrapper); an
  unknown root name (`cli.root`), a malformed certificate (`cert.parse`) and
  another program's certificate (rejected by the table check). -/

namespace CompilatrixTests.Pipeline.Compiler

open Compilatrix Compilatrix.Recheck CompilatrixTests.Src CompilatrixTests.Rt
open System

structure Tools where
  native : Option Rt.Native.Tools := none
  /-- The `compilatrix` binary to spawn; in process when `none`. -/
  bin : Option FilePath := none
  work : FilePath

/-- Run the command line: in process, or the binary. -/
def cli (t : Tools) (args : List String) : IO UInt32 := do
  match t.bin with
  | none => Compilatrix.Cli.main args
  | some b =>
    let out ← IO.Process.output { cmd := b.toString, args := args.toArray }
    unless out.stderr.isEmpty do IO.eprint out.stderr
    pure out.exitCode

/-- A signatures file's roots: name, symbol, parameters, type and sig. -/
def readSignatures (f : FilePath) : IO (List (String × String × Nat × Option String × Option String)) := do
  let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile f))
  let roots ← IO.ofExcept (j.getObjValAs? (Array Lean.Json) "roots")
  roots.toList.mapM fun r => IO.ofExcept do
    let name ← r.getObjValAs? String "name"
    let symbol ← r.getObjValAs? String "symbol"
    let params ← r.getObjValAs? Nat "params"
    let ty := (r.getObjValAs? String "type").toOption
    let sig := (r.getObjValAs? String "sig").toOption
    pure (name, symbol, params, ty, sig)

/-- Native runs of one root at the test and bench sizes, through the
driver's decoder with the printed signature. -/
def runSizes (a : Assert) (nt : Rt.Native.Tools) (label bench : String) (object : ByteArray) (symbol : String)
    (ty sig : Option String) : IO String := do
  let (testArgs, testWant) ← CompilatrixTests.Src.Bench.testCase bench
  let (benchArgs, benchWant) ← CompilatrixTests.Rt.Levels.benchCase bench
  let exe ← link nt label object symbol
  let tyArgs := match ty, sig with
    | some t, some s => some (t, s)
    | _, _ => none
  let nat : Option (Compilatrix.Rt.Sig × Compilatrix.Rt.FoTy) :=
    tyArgs.bind fun (t, s) => if t == "n" && s == "" then some ({}, .nat) else none
  let o : Rt.Native.Options := { stack := 1 <<< 28, time := true, ty := nat }
  expect a o.ty.isSome s!"{label}: the signature {ty} {sig} is not Nat's"
  let lines ← Rt.Native.run exe o [testArgs, benchArgs]
  let mut ns := []
  for ((xs, want), l) in [(testArgs, testWant), (benchArgs, benchWant)].zip lines do
    expect a (l.status == 0 && l.ok) s!"{label} {xs}: status {l.status}, registers restored {l.ok}"
    expect a (l.obs == some (toString want)) s!"{label} {xs}: the driver reads back {l.obs}, expected {want}"
    ns := ns ++ [l.ns.getD 0]
  pure s!"test {testArgs} = {testWant} in {ns[0]!} ns, bench {benchArgs} = {benchWant} in {ns[1]!} ns"

/-- The command line on one closure: compile, check the certificate,
recompile from it, and (natively) run each root. -/
def closure (a : Assert) (t : Tools) (label : String) (ixe eqs : FilePath)
    (roots : List (String × String)) (typecheck : Bool) : IO (Array String) := do
  let obj := t.work / s!"{label}.o"
  let cert := t.work / s!"{label}.cert.json"
  let sigs := t.work / s!"{label}.sig.json"
  let rootArgs := roots.flatMap fun (r, _) => ["--root", r]
  -- erased typing on the first compile only (when asked); the recompiles skip it
  let common := [ixe.toString, "--equations", eqs.toString] ++ rootArgs ++ ["--no-typecheck"]
  let first := [ixe.toString, "--equations", eqs.toString] ++ rootArgs ++
    (if typecheck then [] else ["--no-typecheck"])
  let (code, ms) ← timed (cli t (["compile"] ++ first ++ ["-o", obj.toString, "--emit-cert", cert.toString,
    "--signatures", sigs.toString]))
  expectEq a code 0 s!"{label}: compile exit code"
  let object ← IO.FS.readBinFile obj
  -- the certificate alone reproduces the object
  let code ← cli t (["check-cert"] ++ common ++ ["--cert", cert.toString])
  expectEq a code 0 s!"{label}: check-cert exit code"
  let obj2 := t.work / s!"{label}.from-cert.o"
  let code ← cli t (["compile"] ++ common ++ ["--cert", cert.toString, "-o", obj2.toString])
  expectEq a code 0 s!"{label}: compile --cert exit code"
  expect a ((← IO.FS.readBinFile obj2) == object) s!"{label}: compile --cert wrote a different object"
  let signatures ← readSignatures sigs
  expectEq a signatures.length roots.length s!"{label}: signatures"
  let mut out := #[s!"{label}: compiled in {ms} ms{if typecheck then " (with erased typing)" else ""}, \
    object {object.size} bytes, certificate {(← IO.FS.readFile cert).utf8ByteSize} bytes; \
    check-cert and compile --cert agree"]
  for ((name, bench), (name', symbol, params, ty, sig)) in roots.zip signatures do
    expectEq a name' name s!"{label}: root order"
    expectEq a params (CompilatrixTests.Rt.Levels.modelArgs bench).head!.length s!"{label} {name}: parameters"
    if let some nt := t.native then
      let line ← runSizes a nt s!"{label}_{name.replace "." "_"}" bench object symbol ty sig
      out := out.push s!"  {name} ({symbol}): {line}"
  return out

/-- Every bench-k1 closure, and `k1.ixe` with its five roots. Erased typing
runs in the first compile of fib, tak and gcd (under 0.5 s each); sum-loop,
ackermann (35–40 s each) and `k1.ixe` (about 43 s) skip it here, as do the
recompiles (`tests-ixon-v3` types every K1 closure). -/
def commandLine (a : Assert) (t : Tools) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let typecheck := !(name == "sum-loop" || name == "ackermann")
    out := out ++ (← closure a t name (benchIxe name) (benchEqs name) [("entry", name)] typecheck)
  out := out ++ (← closure a t "k1" k1Ixe k1Eqs k1Roots false)
  return out

/-! ## The object the stage suites make -/

def sameObject (a : Assert) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let inp ← benchInput name
    let (_, art) ← compileIn name inp { names := [name], provenance := some Rt.Machine.testProvenance }
    let (S, _) ← CompilatrixTests.Rt.Differential.entry name
    let c ← IO.ofExcept ((Rt.Machine.compile S.lir).mapError (s!"{name}: " ++ ·))
    expect a (art.object == c.artifact.object)
      s!"{name}: produce + run made a different object from the stage suites' pipeline"
    expect a (art.lowered.program.text == S.lir.program.text) s!"{name}: Lir differs"
    out := out.push s!"{name}: identical object ({art.object.size} bytes) and Lir"
  return out

/-! ## Round trips -/

def roundTrip (a : Assert) (label : String) (inp : Input) : IO String := do
  let (c, art) ← compileIn label inp
  let text := c.toText
  let c' ← ofErr label fun _ => Cert.ofText text
  expectEq a c'.toText text s!"{label}: the certificate's JSON does not round-trip"
  let art' ← ofErr label fun _ => run (Config.forInput {} inp) inp.program c'
  expect a (art'.object == art.object) s!"{label}: the parsed certificate makes a different object"
  pure s!"{label}: {text.utf8ByteSize} bytes of JSON round-trip; the same object"

def roundTrips (a : Assert) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    out := out.push (← roundTrip a name (← benchInput name))
  out := out.push (← roundTrip a "k1" (← ingressFile k1Ixe k1Eqs (k1Roots.map (·.1))))
  return out

/-! ## Declines and rejections -/

def expectErr {α : Type} (a : Assert) (label : String) (r : Except Err α) (stage : Stage) (code : String) :
    IO String := do
  match r with
  | .ok _ => expect a false s!"{label}: accepted, expected {stage.name}: {code}"; pure ""
  | .error e =>
    expect a (e.stage == stage && e.code == code) s!"{label}: {e.render}, expected {stage.name}: {code}"
    pure s!"{label}: {(e.render.take 150).toString}"

/-- A root with `n` `Nat` parameters returning the first (hand-written Fir). -/
def wide (n : Nat) : Cfg.Program :=
  Cases.cfgOf (Cases.prog [((List.range n), .ret (Cases.v 0))])

def declines (a : Assert) (t : Tools) : IO (Array String) := do
  let mut out := #[]
  -- the fallback route: no equations, so the middle end keeps closures
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile k1Eqs))
  let noEqs := json.setObjVal! "equations" (Lean.Json.arr #[])
  let noEqsFile := t.work / "k1-no-equations.json"
  IO.FS.writeFile noEqsFile noEqs.pretty
  let bytes ← IO.FS.readBinFile k1Ixe
  for (root, _) in k1Roots do
    out := out.push (← expectErr a s!"fallback route {root}"
      (compile {} bytes noEqs [root] (typecheck := false)) .fir "fir.closures")
  let code ← cli t ["compile", k1Ixe.toString, "--equations", noEqsFile.toString, "--root", "K1.fib",
    "--no-typecheck", "-o", (t.work / "fallback.o").toString]
  expectEq a code 1 "fallback route: the command line's exit code"
  -- six parameters: declined before lowering; five are fine
  out := out.push (← expectErr a "six parameters" (checkParams { names := ["wide"] } (wide 6) [(0, 0)])
    .rt "rt.params")
  match checkParams {} (wide 5) [(0, 0)] with
  | .ok () => expect a true ""
  | .error e => expect a false s!"five parameters: {e.render}"
  -- without the check, the backend would reject the wrapper
  let l ← IO.ofExcept ((Compilatrix.Rt.lower {} (wide 6)).mapError (·.render))
  match l.compile Rt.Machine.testProvenance with
  | .error (.stacking (.export ..)) => expect a true ""
  | .error e => expect a false s!"six parameters without the check: {e}"
  | .ok _ => expect a false "six parameters without the check: the backend accepted it"
  out := out.push "  (without the check, stacking rejects the six-parameter wrapper: stacking.export)"
  -- names, certificates
  out := out.push (← expectErr a "unknown root" (ingress bytes json ["K1.nope"] false) .cli "cli.root")
  out := out.push (← expectErr a "malformed certificate" (Cert.ofText "{\"format\": \"compilatrix/cert/1\"}")
    .cert "cert.parse")
  out := out.push (← expectErr a "a certificate of another format" (Cert.ofText "{\"format\": \"x\"}")
    .cert "cert.parse")
  let (gcdCert, _) ← compileIn "gcd" (← benchInput "gcd")
  let tak ← benchInput "tak"
  out := out.push (← expectErr a "gcd's certificate on tak" (run (Config.forInput {} tak) tak.program gcdCert)
    .table "table.entry")
  let code ← cli t ["compile", "--bogus"]
  expectEq a code 2 "a usage error's exit code"
  return out

end CompilatrixTests.Pipeline.Compiler
