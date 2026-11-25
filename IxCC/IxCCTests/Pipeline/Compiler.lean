import IxCCTests.Pipeline.Support
import IxCCTests.Rt.Differential
import IxCCTests.Rt.Cases
import IxCCTests.Lam.Differential
import IxCC.CompileClaim
import IxCCTests.Recheck.Hostile
import IxCCTests.Src.AutoHints

/-! The compiler: the `ixcc` command line on the fixtures,
`produce` + `Recheck.run` against the stage suites' pipelines, the
certificate's serialisation, and the declines.

* **The command line** (`IxCC.Cli.main`, in process, or the built
  binary with `--bin`): each bench-k1 closure is compiled to an object with
  its certificate and signatures; `check-cert` accepts the certificate, and
  `compile --cert` with it writes the identical object (the recheck needs
  nothing from `produce`). `k1.ixe` is compiled with its five roots into
  one object exporting `cx_K1_fib` … `cx_K1_gcd`. With `--native`, every
  object runs as a test executable for each root at the manifest's test and
  bench sizes against `expected.txt` and `bench_expected`, its result read
  back at the type and signature the compiler printed.
* **The same object**: `produce` then `run` makes byte for byte the object
  the stage suites' pipeline makes today (`Src.load`, `Lam.erase`,
  `Anf.Pipeline.produce`, `Cfg.ofAnf`, `Rt.lower`, `Select.run`,
  `Alloc.run`, `Backend.emit`; `IxCCTests.Rt.Machine.compile`).
* **Round trips**: the certificate's JSON parses back to a certificate with
  the same JSON, and `run` on it makes the same object.
* **Failing closed** (`failClosed`): the uncertified modes, outputs all or nothing, the exit
  statuses, `--embed-cert`'s executable verifier and `verify-exe`'s `--expect-*`.
* **Declines**: the fallback route (a sidecar without equations), declined
  at `fir` with `fir.closures` before the closures step, compiles; a root
  with six parameters with
  `rt.params` (without the check, stacking would reject its wrapper); an
  unknown root name (`cli.root`), a malformed certificate (`cert.parse`) and
  another program's certificate (rejected by the table check). -/

namespace IxCCTests.Pipeline.Compiler

open IxCC IxCC.Recheck IxCCTests.Src IxCCTests.Rt
open System

structure Tools where
  native : Option Rt.Native.Tools := none
  /-- The `ixcc` binary to spawn; in process when `none`. -/
  bin : Option FilePath := none
  work : FilePath

/-- Run the command line: in process, or the binary. -/
def cli (t : Tools) (args : List String) : IO UInt32 := do
  match t.bin with
  | none => IxCC.Cli.main args
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
  let (testArgs, testWant) ← IxCCTests.Src.Bench.testCase bench
  let (benchArgs, benchWant) ← IxCCTests.Rt.Levels.benchCase bench
  let exe ← link nt label object symbol
  let tyArgs := match ty, sig with
    | some t, some s => some (t, s)
    | _, _ => none
  let nat : Option (IxCC.Rt.Sig × IxCC.Rt.FoTy) :=
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
    (roots : List (String × String)) : IO (Array String) := do
  let obj := t.work / s!"{label}.o"
  let cert := t.work / s!"{label}.cert.json"
  let sigs := t.work / s!"{label}.sig.json"
  let rootArgs := roots.flatMap fun (r, _) => ["--root", r]
  let common := [ixe.toString, "--equations", eqs.toString] ++ rootArgs
  let first := common
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
  let mut out := #[s!"{label}: compiled in {ms} ms, \
    object {object.size} bytes, certificate {(← IO.FS.readFile cert).utf8ByteSize} bytes; \
    check-cert and compile --cert agree"]
  for ((name, bench), (name', symbol, params, ty, sig)) in roots.zip signatures do
    expectEq a name' name s!"{label}: root order"
    expectEq a params (IxCCTests.Rt.Levels.modelArgs bench).head!.length s!"{label} {name}: parameters"
    if let some nt := t.native then
      let line ← runSizes a nt s!"{label}_{name.replace "." "_"}" bench object symbol ty sig
      out := out.push s!"  {name} ({symbol}): {line}"
  return out

/-- Exercise `--rc off`, `--rc auto`, and `--rc on` (including `check-cert` and
`compile --cert` on `ixcc/rc-cert/2` certificates) on both a scalar K1 closure
(`gcd` -> `.zeroRc`) and a heap RC closure (`reverseList` -> `.plainRc`). -/
def rcCommandLine (a : Assert) (t : Tools) : IO (Array String) := do
  let gcdIxe := (benchIxe "gcd").toString
  let gcdEqs := (benchEqs "gcd").toString
  let gcdOffObj := t.work / "gcd.o"
  let gcdAutoObj := t.work / "gcd.rc-auto.o"
  let gcdAutoCert := t.work / "gcd.rc-auto.cert.json"
  let code ← cli t ["compile", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--rc", "auto", "-o", gcdAutoObj.toString, "--emit-cert", gcdAutoCert.toString]
  expectEq a code 0 "gcd --rc auto: compile exit code"
  expect a ((← IO.FS.readBinFile gcdAutoObj) == (← IO.FS.readBinFile gcdOffObj))
    "gcd --rc auto: object differs from --rc off"
  let gcdAutoCertText := (← IO.FS.readFile gcdAutoCert).trimAscii.toString
  expect a (!gcdAutoCertText.startsWith "[\"ixcc/rc-cert/2\"")
    "gcd --rc auto: scalar closure should emit ixcc/cert/1"
  let gcdOnObj := t.work / "gcd.rc-on.o"
  let gcdOnCert := t.work / "gcd.rc-on.cert.json"
  let code ← cli t ["compile", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--rc", "on", "-o", gcdOnObj.toString, "--emit-cert", gcdOnCert.toString]
  expectEq a code 0 "gcd --rc on: compile exit code"
  let gcdOnCertText := (← IO.FS.readFile gcdOnCert).trimAscii.toString
  expect a (gcdOnCertText.startsWith "[\"ixcc/rc-cert/2\"")
    "gcd --rc on: should emit ixcc/rc-cert/2"
  let code ← cli t ["check-cert", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--cert", gcdOnCert.toString]
  expectEq a code 0 "gcd --rc on: check-cert exit code"
  let gcdFromRcCertObj := t.work / "gcd.from-rc-cert.o"
  let code ← cli t ["compile", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--cert", gcdOnCert.toString, "-o", gcdFromRcCertObj.toString]
  expectEq a code 0 "gcd --rc on: compile --cert exit code"
  expect a ((← IO.FS.readBinFile gcdFromRcCertObj) == (← IO.FS.readBinFile gcdOnObj))
    "gcd --rc on: compile --cert wrote a different object"
  -- Heap RC closure (`reverseList`): `--rc auto` selects `.plainRc` and matches `--rc on`
  let rcIxe := "fixtures/rc/real-source/anonymous.ixe"
  let rcEqs := "fixtures/rc/real-source/consumer.equations.json"
  let rcRoot := "IxCCTests.Own.H0.reverseList"
  let revAutoObj := t.work / "reverseList.rc-auto.o"
  let revAutoCert := t.work / "reverseList.rc-auto.cert.json"
  let code ← cli t ["compile", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--rc", "auto", "-o", revAutoObj.toString, "--emit-cert", revAutoCert.toString]
  expectEq a code 0 "reverseList --rc auto: compile exit code"
  let revAutoCertText := (← IO.FS.readFile revAutoCert).trimAscii.toString
  expect a (revAutoCertText.startsWith "[\"ixcc/rc-cert/2\"")
    "reverseList --rc auto: heap closure should emit ixcc/rc-cert/2"
  let revOnObj := t.work / "reverseList.rc-on.o"
  let revOnCert := t.work / "reverseList.rc-on.cert.json"
  let code ← cli t ["compile", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--rc", "on", "-o", revOnObj.toString, "--emit-cert", revOnCert.toString]
  expectEq a code 0 "reverseList --rc on: compile exit code"
  expect a ((← IO.FS.readBinFile revAutoObj) == (← IO.FS.readBinFile revOnObj))
    "reverseList: --rc auto and --rc on objects differ"
  expectEq a revAutoCertText ((← IO.FS.readFile revOnCert).trimAscii.toString)
    "reverseList: --rc auto and --rc on certificates differ"
  let code ← cli t ["check-cert", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--cert", revAutoCert.toString]
  expectEq a code 0 "reverseList --rc auto: check-cert exit code"
  let revFromCertObj := t.work / "reverseList.from-rc-cert.o"
  let code ← cli t ["compile", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--cert", revAutoCert.toString, "-o", revFromCertObj.toString]
  expectEq a code 0 "reverseList --rc auto: compile --cert exit code"
  expect a ((← IO.FS.readBinFile revFromCertObj) == (← IO.FS.readBinFile revAutoObj))
    "reverseList --rc auto: compile --cert wrote a different object"
  return #["--rc auto/on: gcd selects zeroRc (ixcc/cert/1), reverseList selects plainRc (ixcc/rc-cert/2); check-cert and compile --cert agree"]

/-- Run the CLI capturing stdout/stderr and exit code (in process or via binary). -/
private def cliCapture (t : Tools) (args : List String) : IO (UInt32 × String) := do
  match t.bin with
  | none =>
    let (out, code) ← IO.FS.withIsolatedStreams (IxCC.Cli.main args)
    pure (code, out)
  | some b =>
    let r ← IO.Process.output { cmd := b.toString, args := args.toArray }
    pure (r.exitCode, r.stdout ++ r.stderr)

/-- Read the `(name?, address)` root pairs from a sidecar JSON file (for constructing
`--root NAME=ADDR` specs in equivalence tests). -/
private def sidecarRootsOf (eqs : FilePath) : IO (Array (IxCC.Ixon.Address × Option String)) := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let h ← IO.ofExcept (IxCC.Src.Hints.ofK1Json json)
  pure h.roots

/-- End-to-end auto-hints CLI parity & edge-case tests (no `--equations` sidecar):
byte-identical `.o` across all `bench-k1` closures, `k1.ixe`, `--rc on/auto`, `--opt`,
named `.ixe` (`--root entry` and default root), bare `<64-hex>` (`cx_root0`), `check-cert`,
`--exe --embed-cert` + `verify-exe`, `--stats`, and negative error cases. -/
def autoHintsCommandLine (a : Assert) (t : Tools) : IO (Array String) := do
  let mut out := #[]
  -- 1. All bench-k1 closures: compile WITHOUT --equations vs WITH --equations
  for name in benchNames do
    let rs ← sidecarRootsOf (benchEqs name)
    let some (entryAddr, _) := rs[0]? | throw (IO.userError s!"{name}: missing sidecar root")
    let autoObj := t.work / s!"{name}.auto.o"
    let autoCert := t.work / s!"{name}.auto.cert.json"
    let (code, statsOut) ← cliCapture t ["compile", (benchIxe name).toString,
      "--root", s!"entry={entryAddr}", "-o", autoObj.toString,
      "--emit-cert", autoCert.toString, "--stats"]
    expectEq a code 0 s!"{name} auto-hints: compile exit code ({statsOut})"
    expect a ((statsOut.splitOn "auto-hints:").length > 1)
      s!"{name} auto-hints: --stats missing 'auto-hints:' line"
    expect a ((← IO.FS.readBinFile autoObj) == (← IO.FS.readBinFile (t.work / s!"{name}.o")))
      s!"{name} auto-hints: object differs from --equations object"
    -- check-cert without --equations
    let (cc, ccOut) ← cliCapture t ["check-cert", (benchIxe name).toString,
      "--root", s!"entry={entryAddr}", "--cert", autoCert.toString]
    expectEq a cc 0 s!"{name} auto-hints: check-cert exit code ({ccOut})"
  -- 2. Multi-root k1.ixe without --equations -> byte-identical to k1.o
  let k1SideRoots ← sidecarRootsOf k1Eqs
  let mut k1AutoRootArgs : List String := []
  for (rName, _) in k1Roots do
    let some (addr, _) := k1SideRoots.find? (·.2 == some rName)
      | throw (IO.userError s!"k1: missing root {rName}")
    k1AutoRootArgs := k1AutoRootArgs ++ ["--root", s!"{rName}={addr}"]
  let k1AutoObj := t.work / "k1.auto.o"
  let (code, k1Out) ← cliCapture t (["compile", k1Ixe.toString] ++ k1AutoRootArgs ++ ["-o", k1AutoObj.toString])
  expectEq a code 0 s!"k1 auto-hints: compile exit code ({k1Out})"
  expect a ((← IO.FS.readBinFile k1AutoObj) == (← IO.FS.readBinFile (t.work / "k1.o")))
    "k1 auto-hints: multi-root object differs from --equations object"
  -- 3. Bare 64-hex address exports cx_root0
  let fibRoots ← sidecarRootsOf (benchEqs "fib")
  let some (fibAddr, _) := fibRoots[0]? | throw (IO.userError "fib: missing root")
  let bareObj := t.work / "fib.bare.o"
  let bareSig := t.work / "fib.bare.sig.json"
  let (code, bareOut) ← cliCapture t ["compile", (benchIxe "fib").toString,
    "--root", toString fibAddr, "-o", bareObj.toString, "--signatures", bareSig.toString]
  expectEq a code 0 s!"fib bare-hex auto-hints: compile exit code ({bareOut})"
  let bareSigs ← readSignatures bareSig
  expect a (bareSigs.head?.map (fun (_, sym, _, _, _) => sym) == some "cx_root0")
    s!"fib bare-hex: expected cx_root0, got {bareSigs}"
  -- 4. Named .ixe: bare --root entry AND omitted --root default to entry, byte-identical to fib.o
  let fibBytes ← IO.FS.readBinFile (benchIxe "fib")
  let namedBytes ← IO.ofExcept (IxCCTests.Src.AutoHints.withNamedMetadata fibBytes [("entry", fibAddr)])
  let namedIxe := t.work / "fib-named.ixe"
  IO.FS.writeBinFile namedIxe namedBytes
  let namedObj1 := t.work / "fib-named-explicit.o"
  let namedObj2 := t.work / "fib-named-default.o"
  let (c1, o1) ← cliCapture t ["compile", namedIxe.toString, "--root", "entry", "-o", namedObj1.toString]
  expectEq a c1 0 s!"named fib --root entry: exit code ({o1})"
  expect a ((← IO.FS.readBinFile namedObj1) == (← IO.FS.readBinFile (t.work / "fib.o")))
    "named fib --root entry: object differs from --equations"
  let (c2, o2) ← cliCapture t ["compile", namedIxe.toString, "-o", namedObj2.toString]
  expectEq a c2 0 s!"named fib default root: exit code ({o2})"
  expect a ((← IO.FS.readBinFile namedObj2) == (← IO.FS.readBinFile (t.work / "fib.o")))
    "named fib default root: object differs from --equations"
  -- 5. --uncertified --opt without --equations -> byte-identical to --equations --uncertified --opt
  let fibOptEq := t.work / "fib.opt.eq.o"
  let fibOptAuto := t.work / "fib.opt.auto.o"
  let (cOptEq, _) ← cliCapture t ["compile", (benchIxe "fib").toString, "--equations", (benchEqs "fib").toString,
    "--root", "entry", "--uncertified", "--opt", "-o", fibOptEq.toString]
  expectEq a cOptEq 0 "fib --uncertified --opt with --equations"
  let (cOptAuto, _) ← cliCapture t ["compile", (benchIxe "fib").toString,
    "--root", s!"entry={fibAddr}", "--uncertified", "--opt", "-o", fibOptAuto.toString]
  expectEq a cOptAuto 0 "fib --uncertified --opt auto-hints"
  expect a ((← IO.FS.readBinFile fibOptAuto) == (← IO.FS.readBinFile fibOptEq))
    "fib --uncertified --opt auto-hints: object differs from --equations --uncertified --opt"
  -- 6. --rc on and --rc auto without --equations on reverseList -> byte-identical to --equations
  let rcIxe := "fixtures/rc/real-source/anonymous.ixe"
  let rcEqs := "fixtures/rc/real-source/consumer.equations.json"
  let rcRoot := "IxCCTests.Own.H0.reverseList"
  let rcSideRoots ← sidecarRootsOf rcEqs
  let some (rcAddr, _) := rcSideRoots.find? (·.2 == some rcRoot)
    | throw (IO.userError "reverseList: missing sidecar root")
  let revAutoOn := t.work / "reverseList.auto.rc-on.o"
  let revAutoAuto := t.work / "reverseList.auto.rc-auto.o"
  let (cRcOn, oRcOn) ← cliCapture t ["compile", rcIxe, "--root", s!"{rcRoot}={rcAddr}",
    "--rc", "on", "-o", revAutoOn.toString]
  expectEq a cRcOn 0 s!"reverseList auto-hints --rc on: exit code ({oRcOn})"
  expect a ((← IO.FS.readBinFile revAutoOn) == (← IO.FS.readBinFile (t.work / "reverseList.rc-on.o")))
    "reverseList auto-hints --rc on: object differs from --equations"
  let (cRcAuto, oRcAuto) ← cliCapture t ["compile", rcIxe, "--root", s!"{rcRoot}={rcAddr}",
    "--rc", "auto", "-o", revAutoAuto.toString]
  expectEq a cRcAuto 0 s!"reverseList auto-hints --rc auto: exit code ({oRcAuto})"
  expect a ((← IO.FS.readBinFile revAutoAuto) == (← IO.FS.readBinFile (t.work / "reverseList.rc-auto.o")))
    "reverseList auto-hints --rc auto: object differs from --equations"
  -- 7. --exe --embed-cert + verify-exe WITHOUT --equations
  let fibExe := t.work / "fib.auto.exe"
  let (cExe, oExe) ← cliCapture t ["compile", (benchIxe "fib").toString,
    "--root", s!"entry={fibAddr}", "--exe", fibExe.toString, "--embed-cert"]
  expectEq a cExe 0 s!"fib auto-hints --exe --embed-cert: exit code ({oExe})"
  let (cVer, oVer) ← cliCapture t ["verify-exe", fibExe.toString]
  expectEq a cVer 0 s!"fib auto-hints verify-exe: exit code ({oVer})"
  -- 8. Negative tests without --equations
  let absentHex := toString (IxCC.Ixon.Address.replicate 0)
  for (lbl, args) in [
    ("anon bare name", ["compile", (benchIxe "fib").toString, "--root", "entry", "-o", (t.work / "bad1.o").toString]),
    ("invalid hex", ["compile", (benchIxe "fib").toString, "--root", "entry=not-valid-hex", "-o", (t.work / "bad2.o").toString]),
    ("0x prefix", ["compile", (benchIxe "fib").toString, "--root", s!"0x{fibAddr}", "-o", (t.work / "bad3.o").toString]),
    ("absent addr", ["compile", (benchIxe "fib").toString, "--root", s!"entry={absentHex}", "-o", (t.work / "bad4.o").toString]),
    ("anon no root", ["compile", (benchIxe "fib").toString, "-o", (t.work / "bad5.o").toString])
  ] do
    let (badCode, _) ← cliCapture t args
    -- each `--root` names nothing in the closure (`cli.root`): a usage error
    expectEq a badCode 2 s!"auto-hints negative ({lbl}) should exit 2"
  out := out.push "auto-hints CLI: byte-identical .o on all 5 bench-k1 + k1.ixe + --uncertified --opt + --rc on/auto + named .ixe (explicit/default) + bare hex (cx_root0) + --exe --embed-cert/verify-exe + 5 negative controls (exit 2)"
  return out

/-- Every bench-k1 closure, and `k1.ixe` with its five roots; each compile
runs the certified kernel's acceptance at ingress (about a second and a half
on the largest closures). -/
def commandLine (a : Assert) (t : Tools) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    out := out ++ (← closure a t name (benchIxe name) (benchEqs name) [("entry", name)])
  out := out ++ (← closure a t "k1" k1Ixe k1Eqs k1Roots)
  out := out ++ (← rcCommandLine a t)
  out := out ++ (← autoHintsCommandLine a t)
  return out

/-! ## The object the stage suites make -/

private def setPiContracts : List Ixon.V3.AllMode → Src.Term → Src.Term
  | c :: cs, .pi b d body => .pi { b with mode := c } d (setPiContracts cs body)
  | _, t => t

private def setLamContracts : List Ixon.V3.AllMode → Src.Term → Src.Term
  | c :: cs, .lam b d body => .lam { b with mode := c } d (setLamContracts cs body)
  | _, t => t

/-- Attach frontend binder modes (`@once` on `build`, `@unique` on `revAcc`,
`@borrowed` on `sumL`) to the `OS16-plain`
heap closure (`build` + `revAcc` + `sumL`) in memory: every producer entry point
refuses it (the kernel annotator's correspondence: its modes are not the
bytes'); with the certificate of the base program's annotation, `Recheck.run`,
`Recheck.runWithContracts` and `CompileClaim.verifyProgram` accept it on the
`.zeroRc` path. -/
def contractZeroRc (a : Assert) : IO String := do
  let ixe : FilePath := "fixtures/ownership/OS16-plain.ixe"
  let eqs : FilePath := "fixtures/ownership/OS16-plain.equations.json"
  let baseInp ← ingressFile ixe eqs ["entry"]
  let p0 := baseInp.program
  let cOnce : Ixon.V3.AllMode := .once
  let cUnique : Ixon.V3.AllMode := .unique
  let cBorrow : Ixon.V3.AllMode := .borrowed
  let lookupEqPair (name : String) : IO (Src.CId × Src.CId) := do
    let some prop := baseInp.hints.proposals.find? (·.name? == some name)
      | throw (IO.userError s!"OS16: missing equation proposal for {name}")
    let some f := p0.lookup prop.subject
      | throw (IO.userError s!"OS16: missing definition {name}")
    let some thm := prop.theorem?.bind p0.lookup
      | throw (IO.userError s!"OS16: missing equation theorem for {name}")
    pure (f, thm)
  let (buildId, buildEqId) ← lookupEqPair "build"
  let (revId, revEqId) ← lookupEqPair "revAcc"
  let (sumId, sumEqId) ← lookupEqPair "sumL"
  let specs : List (Src.CId × Src.CId × List Ixon.V3.AllMode) :=
    [(buildId, buildEqId, [cOnce, cOnce]),
     (revId, revEqId, [cUnique, cUnique]),
     (sumId, sumEqId, [cBorrow, cBorrow])]
  let mut consts := p0.consts
  for (f, thm, cs) in specs do
    let some fEntry := consts.get? f
      | throw (IO.userError s!"OS16: missing const entry for {f}")
    let Src.Decl.defn .defn .safe n tf vf := fEntry.decl
      | throw (IO.userError s!"OS16: unexpected decl for {f}")
    let some thmEntry := consts.get? thm
      | throw (IO.userError s!"OS16: missing eq const entry for {thm}")
    let Src.Decl.defn .thm .safe n' tθ vθ := thmEntry.decl
      | throw (IO.userError s!"OS16: unexpected eq decl for {thm}")
    consts := consts.insert f { fEntry with decl := .defn .defn .safe n (setPiContracts cs tf) (setLamContracts cs vf) }
    consts := consts.insert thm { thmEntry with decl := .defn .thm .safe n' (setPiContracts cs tθ) vθ }
  let annotatedProg : Src.Program := { p0 with consts }
  let annotatedInp : Input := { baseInp with program := annotatedProg }
  let cfg := Config.forInput { names := ["entry"], provenance := some Rt.Machine.testProvenance } annotatedInp
  -- The producer refuses a program that is not its bytes' reading: the kernel
  -- annotator's correspondence compares binder contracts with the kernel's
  -- (every producer entry point: `produce`, `compileInputWithContracts`,
  -- `RcReplay.produceAuto`, `CompileClaim.produce`).
  let refusedByCorr := fun (r : Except Err Unit) => match r with
    | .error e => e.stage == .relevance && e.code == "relevance-oracle" && (e.message.splitOn "contract").length > 1
    | .ok _ => false
  expect a (refusedByCorr ((produce cfg annotatedInp).map fun _ => ()))
    "OS16-contract: produce annotated a program whose contracts are not the bytes'"
  expect a (refusedByCorr ((compileInputWithContracts cfg annotatedInp).map fun _ => ()))
    "OS16-contract: compileInputWithContracts accepted a program whose contracts are not the bytes'"
  expect a (refusedByCorr ((RcReplay.produceAuto cfg annotatedInp).map fun _ => ()))
    "OS16-contract: produceAuto accepted a program whose contracts are not the bytes'"
  expect a ((CompileClaim.produce cfg annotatedInp).toOption.isNone)
    "OS16-contract: CompileClaim.produce accepted a program whose contracts are not the bytes'"
  -- The recheck path on that program (which runs no annotator), with the
  -- certificate the producer made for it before the switch: the base
  -- program's annotation (contracts other than erased ones change no class).
  let (table, _, _) := Src.Table.build cfg.table annotatedProg annotatedInp.hints.proposals
  let ann ← IO.ofExcept (baseInp.kernel.annotateChecked { p0 with table })
  let cert ← ofErr "OS16-contract certificate" fun _ =>
    IxCCTests.Recheck.Hostile.mkCert cfg annotatedProg (Src.Table.TableCert.ofTable table) ann
  let art ← ofErr "OS16-contract run" fun _ => run cfg annotatedProg cert
  let artWithContracts ← ofErr "OS16-contract runWithContracts" fun _ =>
    runWithContracts cfg annotatedProg cert
  expect a (artWithContracts.object == art.object)
    "OS16-contract: runWithContracts agrees with run"
  let hasHeapOps := (List.range art.fir.size).any fun f =>
    (art.fir.fun? f).any fun fd => Own.Plain.codeAllocsOrProjs art.fir.known fd.body
  expect a hasHeapOps "OS16-contract: lowered Fir must allocate or project heap cells"
  expect a (art.rcPolicy == .zeroRc) "OS16-contract: annotated heap program must select zeroRc policy"
  expect a (art.checkContractOwn) "OS16-contract: artifact must pass contract-aware Own.Plain check"
  expect a (checkZeroRcContracts art.fir) "OS16-contract: checkZeroRcContracts must hold"
  expect a (!Own.Plain.Program.check art.fir (Own.Plain.Program.canonical art.fir).bodies)
    "OS16-contract: unannotated Own.Plain.Program.check must reject non-.many contracts"
  expect a (Own.Plain.Program.checkWithContracts art.fir (Own.Plain.Program.canonical art.fir).bodies)
    "OS16-contract: Own.Plain.Program.checkWithContracts must accept annotated heap program"
  let some (rootAddr, _) := annotatedProg.roots.head? | throw (IO.userError "OS16-contract: no root")
  let osClaim : CompileClaim :=
    { env := baseInp.env.root, roleTable := baseInp.env.bindingAddress, target := rootAddr
      policy := .zeroRc, abiArity := 1, elfHash := Ixon.Address.blake3Pure art.object }
  let osCertText := cert.toText
  expect a (CompileClaim.verifyProgram cfg annotatedProg osClaim osCertText)
    "OS16-contract: CompileClaim.verifyProgram must accept valid zeroRc claim"
  let badAddr := Ixon.Address.blake3Pure (ByteArray.mk #[0xde, 0xad, 0xbe, 0xef])
  expect a (!CompileClaim.verifyProgram cfg annotatedProg { osClaim with elfHash := badAddr } osCertText)
    "OS16-contract: CompileClaim.verifyProgram must reject tampered elfHash"
  expect a (!CompileClaim.verifyProgram cfg annotatedProg { osClaim with target := badAddr } osCertText)
    "OS16-contract: CompileClaim.verifyProgram must reject tampered target"
  expect a (!CompileClaim.verifyProgram cfg annotatedProg { osClaim with abiArity := osClaim.abiArity + 1 } osCertText)
    "OS16-contract: CompileClaim.verifyProgram must reject tampered abiArity"
  pure s!"OS16-contract: the producer refuses the heap closure with 1/!/~ contracts set in memory \
    (relevance-oracle: not the bytes' reading); with the base annotation's certificate, run, \
    runWithContracts and CompileClaim.verifyProgram accept it on zeroRc ({art.object.size} bytes)"

/-- Exercise `CompileClaim.produce`, `CompileClaim.verifyProgram`, and
`CompileClaim.verifyBytes` on both `.zeroRc` (`gcd`) and `.plainRc`
(`reverseList`), including negative checks for tampered `elfHash`, `target`,
and `abiArity`. -/
def compileClaims (a : Assert) : IO String := do
  let badAddr := Ixon.Address.blake3Pure (ByteArray.mk #[0xde, 0xad, 0xbe, 0xef])
  -- Scalar K1 fixture (`gcd` -> `.zeroRc` and `.immortal`)
  let gcdBytes ← IO.FS.readBinFile (benchIxe "gcd")
  let gcdJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (benchEqs "gcd")))
  let gcdInp ← benchInput "gcd"
  let gcdCfg : Config := { names := ["entry"], provenance := some Rt.Machine.testProvenance }
  let (gcdClaim, gcdCert, gcdElf) ← ofErr "gcd CompileClaim.produce" fun _ =>
    CompileClaim.produce gcdCfg gcdInp
  expect a (gcdClaim.policy == .zeroRc && gcdClaim.abiArity == 2 &&
      gcdClaim.elfHash == Ixon.Address.blake3Pure gcdElf)
    "gcd CompileClaim: expected zeroRc policy, abiArity 2, and matching PureHash"
  expect a (CompileClaim.verifyProgram gcdCfg gcdInp.program gcdClaim gcdCert)
    "gcd CompileClaim: verifyProgram must accept valid zeroRc claim"
  expect a (CompileClaim.verifyBytes gcdCfg gcdBytes gcdJson gcdClaim gcdCert)
    "gcd CompileClaim: verifyBytes must accept valid zeroRc claim"
  expect a (!CompileClaim.verifyProgram gcdCfg gcdInp.program { gcdClaim with elfHash := badAddr } gcdCert)
    "gcd CompileClaim: verifyProgram must reject tampered elfHash"
  expect a (!CompileClaim.verifyProgram gcdCfg gcdInp.program { gcdClaim with target := badAddr } gcdCert)
    "gcd CompileClaim: verifyProgram must reject tampered target"
  expect a (!CompileClaim.verifyProgram gcdCfg gcdInp.program { gcdClaim with abiArity := gcdClaim.abiArity + 1 } gcdCert)
    "gcd CompileClaim: verifyProgram must reject tampered abiArity"
  expect a (!CompileClaim.verifyBytes gcdCfg gcdBytes gcdJson { gcdClaim with elfHash := badAddr } gcdCert)
    "gcd CompileClaim: verifyBytes must reject tampered elfHash"
  expect a (!CompileClaim.verifyBytes gcdCfg gcdBytes gcdJson { gcdClaim with target := badAddr } gcdCert)
    "gcd CompileClaim: verifyBytes must reject tampered target"
  expect a (!CompileClaim.verifyBytes gcdCfg gcdBytes gcdJson { gcdClaim with abiArity := gcdClaim.abiArity + 1 } gcdCert)
    "gcd CompileClaim: verifyBytes must reject tampered abiArity"
  let (immClaim, immCert, immElf) ← ofErr "gcd CompileClaim.produce immortal" fun _ =>
    CompileClaim.produce gcdCfg gcdInp .immortal
  expect a (immClaim.policy == .immortal && immElf == gcdElf &&
      CompileClaim.verifyProgram gcdCfg gcdInp.program immClaim immCert &&
      CompileClaim.verifyBytes gcdCfg gcdBytes gcdJson immClaim immCert)
    "gcd CompileClaim: immortal policy produce + verifyProgram + verifyBytes"
  -- Heap RC fixture (`reverseList` -> `.plainRc`)
  let rcIxe : FilePath := "fixtures/rc/real-source/anonymous.ixe"
  let rcEqs : FilePath := "fixtures/rc/real-source/consumer.equations.json"
  let rcRoot := "IxCCTests.Own.H0.reverseList"
  let rcBytes ← IO.FS.readBinFile rcIxe
  let rcJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile rcEqs))
  let rcInp ← ingressFile rcIxe rcEqs [rcRoot]
  let rcCfg : Config := { names := [rcRoot], provenance := some Rt.Machine.testProvenance }
  let (rcClaim, rcCert, rcElf) ← ofErr "reverseList CompileClaim.produce" fun _ =>
    CompileClaim.produce rcCfg rcInp
  expect a (rcClaim.policy == .plainRc && rcClaim.abiArity == 2 &&
      rcClaim.elfHash == Ixon.Address.blake3Pure rcElf)
    "reverseList CompileClaim: expected plainRc policy, abiArity 2, and matching PureHash"
  expect a (CompileClaim.verifyProgram rcCfg rcInp.program rcClaim rcCert)
    "reverseList CompileClaim: verifyProgram must accept valid plainRc claim"
  expect a (CompileClaim.verifyBytes rcCfg rcBytes rcJson rcClaim rcCert)
    "reverseList CompileClaim: verifyBytes must accept valid plainRc claim"
  expect a (!CompileClaim.verifyProgram rcCfg rcInp.program { rcClaim with elfHash := badAddr } rcCert)
    "reverseList CompileClaim: verifyProgram must reject tampered elfHash"
  expect a (!CompileClaim.verifyProgram rcCfg rcInp.program { rcClaim with target := badAddr } rcCert)
    "reverseList CompileClaim: verifyProgram must reject tampered target"
  expect a (!CompileClaim.verifyProgram rcCfg rcInp.program { rcClaim with abiArity := rcClaim.abiArity + 1 } rcCert)
    "reverseList CompileClaim: verifyProgram must reject tampered abiArity"
  expect a (!CompileClaim.verifyBytes rcCfg rcBytes rcJson { rcClaim with elfHash := badAddr } rcCert)
    "reverseList CompileClaim: verifyBytes must reject tampered elfHash"
  expect a (!CompileClaim.verifyBytes rcCfg rcBytes rcJson { rcClaim with target := badAddr } rcCert)
    "reverseList CompileClaim: verifyBytes must reject tampered target"
  expect a (!CompileClaim.verifyBytes rcCfg rcBytes rcJson { rcClaim with abiArity := rcClaim.abiArity + 1 } rcCert)
    "reverseList CompileClaim: verifyBytes must reject tampered abiArity"
  -- Wire serialization (`toPayloadBytes`, `toClaimBytes`), roundtrip (`ofPayloadBytes`, `ofClaimBytes`),
  -- commitment (`commit`), deterministic byte vector, and `makeClaim`/`checkClaim`
  expect a (CompilePolicy.immortal.toUInt8 == 0 && CompilePolicy.zeroRc.toUInt8 == 1 &&
      CompilePolicy.plainRc.toUInt8 == 2 && CompilePolicy.ofUInt8? 0 == some .immortal &&
      CompilePolicy.ofUInt8? 1 == some .zeroRc && CompilePolicy.ofUInt8? 2 == some .plainRc &&
      CompilePolicy.ofUInt8? 3 == none)
    "CompilePolicy: wire tag round-trip"
  let vecClaim : CompileClaim := {
    env := ⟨ByteArray.mk (Array.replicate 32 0x11), by decide⟩
    roleTable := none
    target := ⟨ByteArray.mk (Array.replicate 32 0x22), by decide⟩
    policy := .plainRc
    abiArity := 3
    elfHash := ⟨ByteArray.mk (Array.replicate 32 0x33), by decide⟩
  }
  -- The claim names the role table (`roleTable`, validator `07`). ix's `Tests/Ix/Claim.lean`
  -- pins the same vectors: `00` after `env` for an unbound environment, `01` and the
  -- table's address for a role-bound one; the former format (validator `06`, no role
  -- table) is refused.
  let expectedVecBytes : ByteArray :=
    ByteArray.mk (#[0xE8, 0x05, 0x04, 0x07] ++
      Array.replicate 32 0x11 ++ #[0x00] ++
      Array.replicate 32 0x22 ++
      #[0x02, 0x03] ++
      Array.replicate 32 0x33)
  let boundVecClaim : CompileClaim :=
    { vecClaim with roleTable := some ⟨ByteArray.mk (Array.replicate 32 0x44), by decide⟩ }
  let expectedBoundVecBytes : ByteArray :=
    ByteArray.mk (#[0xE8, 0x05, 0x04, 0x07] ++
      Array.replicate 32 0x11 ++ #[0x01] ++ Array.replicate 32 0x44 ++
      Array.replicate 32 0x22 ++
      #[0x02, 0x03] ++
      Array.replicate 32 0x33)
  let formerVecBytes : ByteArray :=
    ByteArray.mk (#[0xE8, 0x05, 0x04, 0x06] ++
      Array.replicate 32 0x11 ++
      Array.replicate 32 0x22 ++
      #[0x02, 0x03] ++
      Array.replicate 32 0x33)
  expect a (vecClaim.toClaimBytes == expectedVecBytes &&
      vecClaim.toClaimBytes.size == 103 &&
      CompileClaim.ofClaimBytes vecClaim.toClaimBytes == some vecClaim &&
      CompileClaim.ofPayloadBytes vecClaim.toPayloadBytes == some vecClaim)
    "CompileClaim: deterministic 103-byte wire vector (#[0xE8, 0x05, 0x04, 0x07, ...], no role table) and roundtrip"
  expect a (boundVecClaim.toClaimBytes == expectedBoundVecBytes &&
      boundVecClaim.toClaimBytes.size == 135 &&
      CompileClaim.ofClaimBytes boundVecClaim.toClaimBytes == some boundVecClaim &&
      CompileClaim.ofPayloadBytes boundVecClaim.toPayloadBytes == some boundVecClaim)
    "CompileClaim: deterministic 135-byte wire vector with a role table, and roundtrip"
  expect a (CompileClaim.ofClaimBytes formerVecBytes == none &&
      CompileClaim.ofClaimBytes (formerVecBytes.set! 3 0x07) == none &&
      CompileClaim.ofClaimBytes (expectedVecBytes.set! 3 0x06) == none &&
      CompileClaim.ofClaimBytes (expectedVecBytes.set! 36 0x02) == none)
    "CompileClaim: the former format (validator 06, no role table), either header over the other payload, and an invalid role-table tag are refused"
  -- `abiArity` is ix's `N0` code. ix's `Tests/Ix/Claim.lean` pins the same
  -- vectors: one byte below 128, then the TagN rungs; `80 80` is 256 (IxCC's former
  -- Tag0 spelling of 128); the invalid code `C4` and the code of `2 ^ 64` are refused.
  let arityClaimBytes (arity : List UInt8) : ByteArray :=
    ByteArray.mk (#[0xE8, 0x05, 0x04, 0x07] ++ Array.replicate 32 0x11 ++ #[0x00] ++
      Array.replicate 32 0x22 ++ #[0x02] ++ arity.toArray ++ Array.replicate 32 0x33)
  let arityVectors : List (Nat × List UInt8) := [
    (0, [0x00]), (5, [0x05]), (6, [0x06]), (127, [0x7F]), (128, [0x80, 0x00]),
    (256, [0x80, 0x80]), (16511, [0xBF, 0xFF]), (16512, [0xC0, 0x00, 0x00]),
    (2 ^ 64 - 1, [0xC3, 0x7F, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF])]
  let arityRejected : List (List UInt8) :=
    [[0xC4], [0xC3, 0x80, 0xBF, 0xFE, 0xFE, 0xFE, 0xFF, 0xFF, 0xFF]]
  expect a (arityVectors.all fun (arity, bytes) =>
      let claim := { vecClaim with abiArity := arity }
      claim.toClaimBytes == arityClaimBytes bytes &&
        CompileClaim.ofClaimBytes (arityClaimBytes bytes) == some claim)
    "CompileClaim: abiArity N0 vectors shared with ix's Claim.ser"
  expect a (arityRejected.all fun bytes => CompileClaim.ofClaimBytes (arityClaimBytes bytes) == none)
    "CompileClaim: invalid and overflowing abiArity codes are refused"
  expect a (CompileClaim.ofClaimBytes (vecClaim.toClaimBytes.set! 1 0x03) == none &&
      CompileClaim.ofClaimBytes (vecClaim.toClaimBytes.set! 1 0x04) == none)
    "CompileClaim: the role-binding (E8 03) and literal-class (E8 04) tags are not compile claims"
  let gcdClaimBytes := gcdClaim.toClaimBytes
  -- every committed closure is role-bound: the claim names its role table (135 bytes)
  expect a (gcdClaimBytes.size == 135 && gcdClaim.roleTable.isSome &&
      gcdClaimBytes.get! 0 == 0xE8 && gcdClaimBytes.get! 1 == 0x05 &&
      gcdClaimBytes.get! 2 == 0x04 && gcdClaimBytes.get! 3 == 0x07 &&
      gcdClaimBytes.get! 36 == 1 && gcdClaimBytes.get! 101 == 1 && gcdClaimBytes.get! 102 == 2 &&
      CompileClaim.ofClaimBytes gcdClaimBytes == some gcdClaim &&
      CompileClaim.ofPayloadBytes gcdClaim.toPayloadBytes == some gcdClaim &&
      gcdClaim.commit == Ixon.Address.blake3Pure gcdClaimBytes)
    "gcd CompileClaim: wire envelope layout (#[0xE8, 0x05, 0x04, 0x07, ...], the role table), roundtrip, and deterministic BLAKE3 commit"
  let rcClaimBytes := rcClaim.toClaimBytes
  expect a (rcClaimBytes.size == 135 && rcClaim.roleTable.isSome &&
      rcClaimBytes.get! 0 == 0xE8 && rcClaimBytes.get! 1 == 0x05 &&
      rcClaimBytes.get! 2 == 0x04 && rcClaimBytes.get! 3 == 0x07 &&
      rcClaimBytes.get! 36 == 1 && rcClaimBytes.get! 101 == 2 && rcClaimBytes.get! 102 == 2 &&
      CompileClaim.ofClaimBytes rcClaimBytes == some rcClaim &&
      CompileClaim.ofPayloadBytes rcClaim.toPayloadBytes == some rcClaim &&
      rcClaim.commit == Ixon.Address.blake3Pure rcClaimBytes &&
      rcClaim.commit != gcdClaim.commit)
    "reverseList CompileClaim: wire envelope layout (#[0xE8, 0x05, 0x04, 0x07, ...], the role table), roundtrip, and deterministic BLAKE3 commit"
  let (madeGcdClaim, madeGcdCert, madeGcdElf) ← IO.ofExcept (CompileClaim.makeClaim gcdCfg gcdBytes gcdJson)
  expect a (madeGcdClaim == gcdClaim && madeGcdCert == gcdCert && madeGcdElf == gcdElf &&
      (CompileClaim.checkClaim gcdCfg gcdBytes gcdJson madeGcdClaim madeGcdCert).isOk &&
      !(CompileClaim.checkClaim gcdCfg gcdBytes gcdJson { madeGcdClaim with elfHash := badAddr } madeGcdCert).isOk)
    "gcd CompileClaim: makeClaim and checkClaim agree with produce/verifyBytes"
  let (madeRcClaim, madeRcCert, madeRcElf) ← IO.ofExcept (CompileClaim.makeClaim rcCfg rcBytes rcJson)
  expect a (madeRcClaim == rcClaim && madeRcCert == rcCert && madeRcElf == rcElf &&
      (CompileClaim.checkClaim rcCfg rcBytes rcJson madeRcClaim madeRcCert).isOk &&
      !(CompileClaim.checkClaim rcCfg rcBytes rcJson { madeRcClaim with elfHash := badAddr } madeRcCert).isOk)
    "reverseList CompileClaim: makeClaim and checkClaim agree with produce/verifyBytes"
  pure s!"CompileClaim: zeroRc (gcd {gcdElf.size}B) and plainRc (reverseList {rcElf.size}B) verified end-to-end with wire commit and makeClaim/checkClaim; tampered claims rejected"

def sameObject (a : Assert) : IO (Array String) := do
  let mut out := #[]
  for name in benchNames do
    let inp ← benchInput name
    let (_, art) ← compileIn name inp { names := [name], provenance := some Rt.Machine.testProvenance }
    let (S, _) ← IxCCTests.Rt.Differential.entry name
    let c ← IO.ofExcept ((Rt.Machine.compile S.lir).mapError (s!"{name}: " ++ ·))
    expect a (art.object == c.artifact.object)
      s!"{name}: produce + run made a different object from the stage suites' pipeline"
    expect a (art.lowered.program.text == S.lir.program.text) s!"{name}: Lir differs"
    out := out.push s!"{name}: identical object ({art.object.size} bytes) and Lir"
  out := out.push (← contractZeroRc a)
  out := out.push (← compileClaims a)
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
  -- the fallback route: no equations, so the middle end keeps closures, which the
  -- closures step removes (the defun part runs these objects natively)
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile k1Eqs))
  let noEqs := json.setObjVal! "equations" (Lean.Json.arr #[])
  let noEqsFile := t.work / "k1-no-equations.json"
  IO.FS.writeFile noEqsFile noEqs.pretty
  let bytes ← IO.FS.readBinFile k1Ixe
  for (root, _) in k1Roots do
    match compile {} bytes noEqs [root] with
    | .ok (_, art) =>
      expect a (Anf.firstOrder art.anf) s!"fallback route {root}: the program Fir lowers is not first order"
      expect a (Anf.Pipeline.residual art.anf).fns.isEmpty s!"fallback route {root}: a local function is left"
      out := out.push s!"fallback route {root}: compiled through the closures step ({art.object.size} bytes)"
    | .error e => expect a false s!"fallback route {root}: {e.render}, expected it to compile"
  let code ← cli t ["compile", k1Ixe.toString, "--equations", noEqsFile.toString, "--root", "K1.fib",
    "-o", (t.work / "fallback.o").toString]
  expectEq a code 0 "fallback route: the command line's exit code"
  -- six parameters: declined before lowering; five are fine
  out := out.push (← expectErr a "six parameters" (checkParams { names := ["wide"] } (wide 6) [(0, 0)])
    .rt "rt.params")
  match checkParams {} (wide 5) [(0, 0)] with
  | .ok () => expect a true ""
  | .error e => expect a false s!"five parameters: {e.render}"
  -- without the check, the backend would reject the wrapper
  let l ← IO.ofExcept ((IxCC.Rt.lower {} (wide 6)).mapError (·.render))
  match l.compile Rt.Machine.testProvenance with
  | .error (.stacking (.export ..)) => expect a true ""
  | .error e => expect a false s!"six parameters without the check: {e}"
  | .ok _ => expect a false "six parameters without the check: the backend accepted it"
  out := out.push "  (without the check, stacking rejects the six-parameter wrapper: stacking.export)"
  -- names, certificates
  out := out.push (← expectErr a "unknown root" (ingress bytes json ["K1.nope"]) .cli "cli.root")
  out := out.push (← expectErr a "malformed certificate" (Cert.ofText "{\"format\": \"ixcc/cert/1\"}")
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

/-! ## Failing closed -/

/-- `needle` occurs in `hay`. -/
private def hasBytes (hay needle : ByteArray) : Bool := Id.run do
  if needle.size == 0 then return true
  if hay.size < needle.size then return false
  for i in [0:hay.size - needle.size + 1] do
    if (hay.extract i (i + needle.size)) == needle then return true
  return false

/-- An object's provenance note: its descriptor and its lowering and pass-policy words. -/
private def notePolicy (object : ByteArray) : Option (ByteArray × Nat × Nat) := do
  let v ← IxCC.X86.ELFRead.parse object
  match v.provenance with
  | .ixir1Policy _ lowering passPolicy => some (v.note.descriptor, lowering, passPolicy)
  | .ixir2 _ => none

/-- The two-constructor enumeration program of `Hostile.enumEnv` (`main : Bool := idc true`), its
`main` asserting `@[no_alloc]`: the closure's bytes and sidecar. -/
def assertsCase : IO (ByteArray × Lean.Json) := do
  let b := IxCCTests.Recheck.Hostile.base (← IxCCTests.Support.Bound.loadBase) 2
  let asserted : IxCC.Ixon.V3.ConstantInfo :=
    .defn { kind := .defn, safety := .safe, asserts := { alloc := .noAlloc }, lvls := 0
            typ := IxCCTests.Recheck.Hostile.enumC, value := .app (.ref 1 #[]) (.ref 2 #[]) }
  let (e, main) := IxCCTests.IxonV3.Builder.store b.env
    ⟨asserted, #[], #[b.enumI, b.idc, b.ctors[1]!], #[], #[]⟩
  pure (IxCCTests.Recheck.Hostile.bytes e, IxCCTests.Recheck.Hostile.sidecar [("main", main)])

/-- `ixcc` failing closed, in process (or the binary with `--bin`):
* **uncertified modes**: `--opt`, `--bignat` (with or without `--opt`) refused without
  `--uncertified` (exit 2, naming what is not covered), `--uncertified` alone refused; with it,
  one line on standard error, and the object's provenance note marked (pass-policy word
  `0x80000002` on lowering 1; the certified object's `(1, 1)`), the executable carrying the same
  note; a program with a definition assertion compiles certified and is declined (exit 1,
  `assert.uncertified`) under `--uncertified --opt` and `--uncertified --bignat`;
* **all or nothing, exit statuses**: a run declined after the object was computed (`--machine`
  on a one-parameter root), a usage error (a missing closure, `--root` naming nothing) and a
  rejection (another program's certificate, `check-cert` and `compile --cert`) each write nothing
  and remove the stale outputs they would have replaced; two outputs naming one file, or an output
  naming an input, are usage errors that leave the input intact; the outcome of each code
  (`Cli.classify`) and the exit statuses the usage text lists;
* **`--embed-cert`**: `Scalar.factorial`, whose executable `verify-exe` rejects (KF-4), is
  rejected (exit 3) and nothing written; `fib`'s is verified and prints its claim; the policy
  recheck refusing is an error, not `immortal`; a verifier refusing the bytes is a rejection;
* **`verify-exe`**: prints the environment root; `--expect-target` and `--expect-env` accept the
  claim's own and reject (exit 3) others; malformed addresses, or the flags on `compile`, are
  usage errors. -/
def failClosed (a : Assert) (t : Tools) : IO (Array String) := do
  let w := t.work / "failclosed"
  IO.FS.createDirAll w
  let has := fun (s needle : String) => (s.splitOn needle).length > 1
  let fibIxe := (benchIxe "fib").toString
  let fibEqs := (benchEqs "fib").toString
  let fib := [fibIxe, "--equations", fibEqs, "--root", "entry"]
  let stale := fun (fs : List FilePath) => fs.forM fun f => IO.FS.writeFile f "stale"
  let noneLeft := fun (label : String) (fs : List FilePath) => fs.forM fun f => do
    expect a (!(← f.pathExists)) s!"{label}: {f} is left behind"
  let mut out := #[]
  -- A. the uncertified modes
  for (flags, needle) in [(["--opt"], "--opt writes an object no certificate covers"),
      (["--bignat"], "--bignat writes an object no certificate covers"),
      (["--bignat", "--opt"], "--bignat writes an object no certificate covers"),
      (["--uncertified"], "--uncertified applies to --opt and --bignat")] do
    let obj := w / "refused.o"
    let (code, msg) ← cliCapture t (["compile"] ++ fib ++ flags ++ ["-o", obj.toString])
    expectEq a code 2 s!"{flags}: exit code"
    expect a (has msg needle) s!"{flags}: the refusal does not say what is not covered: {msg}"
    expect a (has msg "--uncertified") s!"{flags}: the refusal does not name --uncertified: {msg}"
    noneLeft s!"{flags}" [obj]
  let certObj := w / "fib.o"
  let (code, msg) ← cliCapture t (["compile"] ++ fib ++ ["-o", certObj.toString])
  expectEq a code 0 s!"fib: exit code ({msg})"
  expect a (!has msg "uncertified") s!"fib: a certified compile printed an uncertified line: {msg}"
  let optObj := w / "fib.uncertified-opt.o"
  let optExe := w / "fib.uncertified-opt.exe"
  let (code, msg) ← cliCapture t (["compile"] ++ fib ++ ["--uncertified", "--opt", "-o", optObj.toString,
    "--exe", optExe.toString])
  expectEq a code 0 s!"fib --uncertified --opt: exit code ({msg})"
  let warn := (msg.splitOn "\n").filter (·.startsWith "ixcc: uncertified (--opt): ")
  expectEq a warn.length 1 s!"fib --uncertified --opt: uncertified lines in {msg}"
  expect a (warn.all (has · "not covered by certificate replay")) s!"fib --uncertified --opt: {warn}"
  let certNote := notePolicy (← IO.FS.readBinFile certObj)
  let optNote := notePolicy (← IO.FS.readBinFile optObj)
  expect a (certNote.map (·.2) == some (1, 1)) s!"fib: the certified note's words are {certNote.map (·.2)}"
  expect a (optNote.map (·.2) == some (1, 0x80000002))
    s!"fib --uncertified --opt: the note's words are {optNote.map (·.2)}, not (1, 0x80000002)"
  let exeBytes ← IO.FS.readBinFile optExe
  match certNote, optNote with
  | some (certDesc, _), some (optDesc, _) =>
    expect a (hasBytes exeBytes optDesc && !hasBytes exeBytes certDesc)
      "fib --uncertified --opt: the executable does not carry the uncertified note alone"
    expectEq a (certDesc.size, (certDesc.extract 0 (certDesc.size - 8)) == optDesc.extract 0 (optDesc.size - 8))
      (optDesc.size, true) "fib: the notes differ outside their policy words"
  | _, _ => expect a false "fib: a note could not be read"
  out := out.push "uncertified modes: --opt, --bignat, --bignat --opt refused without --uncertified (exit 2), \
    --uncertified alone refused; with it one standard-error line, note words (1, 0x80000002) against \
    the certified (1, 1), the executable carrying the same note"
  -- a definition assertion: checked when certified, declined when uncertified
  let (asBytes, asJson) ← assertsCase
  let asIxe := w / "asserts.ixe"
  let asEqs := w / "asserts.equations.json"
  IO.FS.writeBinFile asIxe asBytes
  IO.FS.writeFile asEqs asJson.pretty
  let asserted := [asIxe.toString, "--equations", asEqs.toString]
  let (code, msg) ← cliCapture t (["compile"] ++ asserted ++ ["-o", (w / "asserts.o").toString])
  expectEq a code 0 s!"@[no_alloc] main: certified compile ({msg})"
  for flags in [["--uncertified", "--opt"], ["--uncertified", "--bignat"]] do
    let obj := w / "asserts.uncertified.o"
    stale [obj]
    let (code, msg) ← cliCapture t (["compile"] ++ asserted ++ flags ++ ["-o", obj.toString])
    expectEq a code 1 s!"@[no_alloc] main {flags}: exit code ({msg})"
    expect a (has msg "assert.uncertified") s!"@[no_alloc] main {flags}: {msg}"
    noneLeft s!"@[no_alloc] main {flags}" [obj]
  out := out.push "definition assertions: @[no_alloc] main compiles certified (checked); \
    --uncertified --opt and --uncertified --bignat decline it (exit 1, assert.uncertified), nothing written"
  -- B. all or nothing, and the exit statuses
  let mOuts := [w / "m.o", w / "m.exe", w / "m.cert", w / "m.sig"]
  stale mOuts
  let (code, msg) ← cliCapture t (["compile"] ++ fib ++ ["-o", (w / "m.o").toString, "--exe", (w / "m.exe").toString,
    "--machine", "--emit-cert", (w / "m.cert").toString, "--signatures", (w / "m.sig").toString])
  expectEq a code 1 s!"fib --exe --machine (one parameter): exit code ({msg})"
  noneLeft "declined after the object was computed" mOuts
  let uOuts := [w / "u.o", w / "u.cert"]
  stale uOuts
  let (code, _) ← cliCapture t ["compile", (w / "missing.ixe").toString, "--equations", fibEqs,
    "-o", (w / "u.o").toString, "--emit-cert", (w / "u.cert").toString]
  expectEq a code 2 "a missing closure: exit code"
  noneLeft "a missing closure" uOuts
  stale uOuts
  let (code, _) ← cliCapture t (["compile", fibIxe, "--equations", fibEqs, "--root", "nosuch",
    "-o", (w / "u.o").toString, "--emit-cert", (w / "u.cert").toString])
  expectEq a code 2 "--root naming no root: exit code"
  noneLeft "--root naming no root" uOuts
  let gcdCert := w / "gcd.cert"
  let (code, _) ← cliCapture t ["compile", (benchIxe "gcd").toString, "--equations", (benchEqs "gcd").toString,
    "-o", (w / "gcd.o").toString, "--emit-cert", gcdCert.toString]
  expectEq a code 0 "gcd: exit code"
  let tak := [(benchIxe "tak").toString, "--equations", (benchEqs "tak").toString]
  let (code, msg) ← cliCapture t (["check-cert"] ++ tak ++ ["--cert", gcdCert.toString])
  expectEq a code 3 s!"check-cert of gcd's certificate on tak: exit code ({msg})"
  let rOuts := [w / "r.o", w / "r.sig"]
  stale rOuts
  let (code, _) ← cliCapture t (["compile"] ++ tak ++ ["--cert", gcdCert.toString, "-o", (w / "r.o").toString,
    "--signatures", (w / "r.sig").toString])
  expectEq a code 3 "compile --cert with gcd's certificate on tak: exit code"
  noneLeft "a rejected certificate" rOuts
  let copy := w / "in.ixe"
  IO.FS.writeBinFile copy (← IO.FS.readBinFile (benchIxe "fib"))
  for args in [["compile", copy.toString, "--equations", fibEqs, "-o", copy.toString],
      ["compile", fibIxe, "--equations", fibEqs, "-o", (w / "c.o").toString, "--emit-cert", (w / "./c.o").toString]] do
    let (code, msg) ← cliCapture t args
    expectEq a code 2 s!"{args}: exit code ({msg})"
  expect a ((← IO.FS.readBinFile copy) == (← IO.FS.readBinFile (benchIxe "fib")))
    "an output naming the input: the input changed"
  let err := fun (code : String) => ({ stage := .cli, code, message := "" } : Err)
  let cases : List (Cli.Outcome × String × Cli.Outcome) := [(.declined, "rt.internal", .internal),
    (.rejected, "cli.read", .usage), (.rejected, "assert.no_alloc", .declined),
    (.rejected, "table.entry", .rejected), (.declined, "erase-string", .declined)]
  for (k, code, want) in cases do
    expect a (Cli.classify k (err code) == want) s!"classify {repr k} {code}"
  let outcomes : List Cli.Outcome := [.declined, .usage, .rejected, .internal]
  expect a (outcomes.map (·.exitCode) == [1, 2, 3, 4])
    "the outcomes' exit statuses"
  expect a (has Cli.usage "1 declined" && has Cli.usage "2 usage error" && has Cli.usage "3 rejected"
    && has Cli.usage "4 internal error" && has Cli.usage "6 declined by a kernel limit")
    "the usage text does not list the exit statuses"
  out := out.push "all or nothing: declined (exit 1), usage (exit 2: missing closure, --root naming nothing, \
    clashing outputs, an output naming the input) and rejected (exit 3: check-cert, compile --cert) runs \
    leave no output, stale ones removed; classify and the exit-status table"
  -- C. --embed-cert runs the executable verifier on its bytes
  let scalar : FilePath := "fixtures/corpus/phase1-scalar"
  let fOuts := [w / "fact.exe", w / "fact.o", w / "fact.cert"]
  stale fOuts
  let (code, msg) ← cliCapture t ["compile", (scalar / "scalar.ixe").toString, "--equations",
    (scalar / "scalar.equations.json").toString, "--root", "Scalar.factorial", "--exe", (w / "fact.exe").toString,
    "--embed-cert", "-o", (w / "fact.o").toString, "--emit-cert", (w / "fact.cert").toString]
  expectEq a code 3 s!"Scalar.factorial --exe --embed-cert: exit code ({msg})"
  expect a (has msg "exe.cert.kf4") s!"Scalar.factorial --embed-cert: not refused by verify-exe's KF-4: {msg}"
  noneLeft "Scalar.factorial --embed-cert" fOuts
  let fibExe := w / "fib.cert.exe"
  let (code, msg) ← cliCapture t (["compile"] ++ fib ++ ["--exe", fibExe.toString, "--embed-cert"])
  expectEq a code 0 s!"fib --exe --embed-cert: exit code ({msg})"
  expect a (has msg "executable certificate verified: target ") s!"fib --embed-cert: no claim line: {msg}"
  let gcdInp ← benchInput "gcd"
  let takInp ← benchInput "tak"
  let (gcdC, gcdArt) ← compileIn "gcd" gcdInp
  match Exe.Cert.policyOfArtifact (Config.forInput {} gcdInp) gcdInp gcdArt false gcdC.toText with
  | .ok p => expect a (p == .zeroRc) s!"gcd: the claim's policy is {repr p}"
  | .error e => expect a false s!"gcd: the claim's policy refused: {e.render}"
  match Exe.Cert.policyOfArtifact (Config.forInput {} takInp) takInp gcdArt false gcdC.toText with
  | .ok p => expect a false s!"a refused contract recheck labelled the claim {repr p}"
  | .error e => expect a (e.code == "exe.cert.policy") s!"a refused contract recheck: {e.render}"
  let fibInp ← benchInput "fib"
  let fibCfg := Config.forInput {} fibInp
  match Cli.compileText .off fibCfg fibInp with
  | .ok (text, cc, art) =>
    let r ← (Cli.embedCertified fibCfg fibInp [] cc text art .plain {} ByteArray.empty ByteArray.empty
      Src.KernelFront.defaultLimits (verify := fun _ => .error (Exe.err "exe.cert.trailer" "refused"))).run
    match r with
    | .error f =>
      expect a (f.outcome == .rejected && f.err.code == "exe.cert.trailer")
        s!"--embed-cert with a refusing verifier: {repr f.outcome} {f.err.render}"
    | .ok _ => expect a false "--embed-cert wrote what its verifier refused"
  | .error e => expect a false s!"fib: compileText: {e.render}"
  out := out.push "--embed-cert: Scalar.factorial (verify-exe's KF-4 refuses it) rejected with nothing written; \
    fib verified and its claim printed; a refused policy recheck an error, not immortal; a refusing \
    verifier a rejection"
  -- D. verify-exe states what it verified, and checks what it is told to expect
  let fibRoots ← sidecarRootsOf (benchEqs "fib")
  let some (fibAddr, _) := fibRoots[0]? | throw (IO.userError "fib: no sidecar root")
  let envRoot := (← IO.ofExcept (IxCC.Ixon.V3.decodeAnonymousEnv (← IO.FS.readBinFile (benchIxe "fib")))).root
  let other := toString (IxCC.Ixon.Address.replicate 7)
  let (code, msg) ← cliCapture t ["verify-exe", fibExe.toString]
  expectEq a code 0 s!"verify-exe: exit code ({msg})"
  expect a (has msg s!"target {fibAddr}" && has msg s!"environment: root {envRoot}")
    s!"verify-exe does not state the target and environment: {msg}"
  let (code, msg) ← cliCapture t ["verify-exe", fibExe.toString, "--expect-target", toString fibAddr,
    "--expect-env", toString envRoot]
  expectEq a code 0 s!"verify-exe with the claim's own target and environment: exit code ({msg})"
  for (flag, needle) in [("--expect-target", "not " ++ other ++ " (--expect-target)"),
      ("--expect-env", "not " ++ other ++ " (--expect-env)")] do
    let (code, msg) ← cliCapture t ["verify-exe", fibExe.toString, flag, other]
    expectEq a code 3 s!"verify-exe {flag} another: exit code ({msg})"
    expect a (has msg needle) s!"verify-exe {flag} another: {msg}"
  for args in [["verify-exe", fibExe.toString, "--expect-target", "xyz"],
      ["verify-exe", fibExe.toString, "--expect-env", "0x" ++ toString fibAddr],
      ["compile"] ++ fib ++ ["-o", (w / "e.o").toString, "--expect-target", toString fibAddr]] do
    let (code, _) ← cliCapture t args
    expectEq a code 2 s!"{args}: exit code"
  out := out.push "verify-exe: target and environment root stated; --expect-target/--expect-env accept the \
    claim's own, reject others (exit 3); malformed or misplaced, usage errors"
  return out

/-! ## Reports -/

/-- The command line's parser, its IR dumps, statistics and signatures
(the parts `compile` prints). -/
def reports (a : Assert) : IO (Array String) := do
  let base := ["compile", "c.ixe", "--equations", "e.json", "-o", "o.o"]
  match IxCC.Cli.parse (base ++ ["--root", "A", "--root", "B", "--dump-ir", "all", "--stats"]) with
  | .ok o => expect a (o.roots == ["A", "B"] && o.dumps == IxCC.Cli.dumpLevels && o.stats && o.rc == .off && !o.opt && !o.bignat) "parse"
  | .error e => expect a false s!"parse: {e}"
  match IxCC.Cli.parse (base ++ ["--uncertified", "--opt"]) with
  | .ok o => expect a (o.opt && o.uncertified) "parse --uncertified --opt"
  | .error e => expect a false s!"parse --uncertified --opt: {e}"
  match IxCC.Cli.parse (base ++ ["--bignat", "--opt", "--bignat-lib", "b.json", "--uncertified"]) with
  | .ok o => expect a (o.bignat && o.opt && o.uncertified && o.bignatLib == some "b.json") "parse --bignat"
  | .error e => expect a false s!"parse --bignat: {e}"
  let addr := toString (IxCC.Ixon.Address.replicate 9)
  match IxCC.Cli.parse ["verify-exe", "a.out", "--expect-target", addr, "--expect-env", addr] with
  | .ok o => expect a (o.expectTarget == some (IxCC.Ixon.Address.replicate 9) &&
      o.expectEnv == some (IxCC.Ixon.Address.replicate 9)) "parse verify-exe --expect-target --expect-env"
  | .error e => expect a false s!"parse verify-exe --expect-target --expect-env: {e}"
  -- optional `--equations`: `compile` and `check-cert` parse cleanly without `--equations`
  match IxCC.Cli.parse ["compile", "c.ixe", "-o", "o.o"] with
  | .ok o => expect a (o.equations.isNone && o.out == some "o.o") "parse compile without --equations"
  | .error e => expect a false s!"parse compile without --equations: {e}"
  match IxCC.Cli.parse ["compile", "c.ixe", "--root", "entry", "-o", "o.o"] with
  | .ok o => expect a (o.equations.isNone && o.roots == ["entry"]) "parse compile --root without --equations"
  | .error e => expect a false s!"parse compile --root without --equations: {e}"
  match IxCC.Cli.parse ["check-cert", "c.ixe", "--cert", "c.json"] with
  | .ok o => expect a (o.equations.isNone && o.cert == some "c.json") "parse check-cert without --equations"
  | .error e => expect a false s!"parse check-cert without --equations: {e}"
  -- a certificate fixes the RC policy: `check-cert` parses without `--rc`, and refuses it (below)
  match IxCC.Cli.parse ["check-cert", "c.ixe", "--equations", "e.json", "--cert", "c.json"] with
  | .ok o => expect a (o.cert.isSome && !o.rcExplicit) "parse check-cert"
  | .error e => expect a false s!"parse check-cert: {e}"
  for (flag, mode) in [("off", IxCC.Cli.RcMode.off), ("on", .on), ("auto", .auto)] do
    match IxCC.Cli.parse (base ++ ["--rc", flag]) with
    | .ok o => expect a (o.rc == mode) s!"parse --rc {flag}"
    | .error e => expect a false s!"parse --rc {flag}: {e}"
  for bad in [["compile", "c.ixe"], ["compile", "c.ixe", "--equations", "e.json"], ["check-cert", "c.ixe",
      "--equations", "e.json"], base ++ ["--dump-ir", "asm"], base ++ ["--rc", "bogus"], ["frobnicate"],
      base ++ ["extra"], base ++ ["--cert", "c.json", "--rc", "auto"],
      base ++ ["--opt", "--cert", "c.json"], base ++ ["--opt", "--emit-cert", "c.json"],
      base ++ ["--exe", "a.out", "--opt", "--embed-cert"],
      base ++ ["--bignat", "--cert", "c.json"], base ++ ["--bignat", "--emit-cert", "c.json"],
      base ++ ["--exe", "a.out", "--bignat", "--embed-cert"],
      base ++ ["--exe", "a.out", "--bignat", "--machine"],
      base ++ ["--bignat", "--rc", "on"], base ++ ["--bignat", "--rc", "auto"],
      base ++ ["--bignat-lib", "b.json"],
      -- the uncertified modes need `--uncertified`, and it needs one of them
      base ++ ["--opt"], base ++ ["--bignat"], base ++ ["--bignat", "--opt"], base ++ ["--uncertified"],
      base ++ ["--uncertified", "--opt", "--cert", "c.json"],
      base ++ ["--exe", "a.out", "--uncertified", "--opt", "--embed-cert"],
      ["check-cert", "c.ixe", "--equations", "e.json", "--cert", "c.json", "--opt"],
      ["check-cert", "c.ixe", "--equations", "e.json", "--cert", "c.json", "--bignat"],
      ["check-cert", "c.ixe", "--equations", "e.json", "--cert", "c.json", "--uncertified", "--opt"],
      ["verify-exe", "a.out", "--opt"],
      ["verify-exe", "a.out", "--bignat"],
      ["verify-exe", "a.out", "--uncertified"],
      -- `--expect-*` take addresses, and only on `verify-exe`
      ["verify-exe", "a.out", "--expect-target", "abc"], ["verify-exe", "a.out", "--expect-env", addr ++ "00"],
      base ++ ["--expect-target", addr], base ++ ["--expect-env", addr],
      -- no two outputs on one file, no output on an input
      base ++ ["--emit-cert", "o.o"], base ++ ["--signatures", "./o.o"], base ++ ["--exe", "c.ixe"],
      ["compile", "c.ixe", "--equations", "e.json", "-o", "e.json"],
      ["check-cert", "c.ixe", "--equations", "e.json", "--cert", "c.json", "--rc", "auto"]] do
    expect a (!(IxCC.Cli.parse bad).toBool) s!"parse accepted {bad}"
  -- every erasure decline renders with its own code
  let eraseCodes := ["erase-const-kind", "erase-string", "erase-mode", "erase-minor", "erase-lazy",
    "erase-proj", "erase-ctor-layout", "erase-C2", "erase-C4", "erase-S2", "erase-scope", "erase-recursor",
    "erase-root", "erase-record", "erase-fuel", "erase-budget", "erase-univs", "erase-unbox-elim",
    "erase-pin", "erase-key", "erase-progwf", "erase-modes"]
  for code in eraseCodes do
    let e := Err.ofErase { code, const := some 7, message := "why" }
    expect a (e.render == s!"erase: {code}: at constant 7: why") s!"erasure's {code} renders as {e.render}"
  let (_, art) ← compileIn "gcd" (← benchInput "gcd")
  let mut sizes := #[]
  for l in IxCC.Cli.dumpLevels do
    let text := IxCC.Cli.dump art l
    expect a (text.length > 20 && !text.startsWith "(no level") s!"--dump-ir {l}: {text.take 80}"
    sizes := sizes.push s!"{l} {text.length}"
  let stats := IxCC.Cli.statsLines art none
  expect a (stats.any (·.startsWith "root entry: cx_entry, parameters 2, driver --type n --sig ''"))
    s!"--stats: {stats}"
  let sig := IxCC.Cli.signaturesJson art
  expect a (sig.compress == "{\"roots\":[{\"name\":\"entry\",\"params\":2,\"sig\":\"\",\"symbol\":\"cx_entry\",\"type\":\"n\"}]}")
    s!"--signatures: {sig.compress}"
  return #[s!"gcd: --dump-ir text sizes {sizes.toList}; {stats.length} --stats lines; signatures {sig.compress}"]

end IxCCTests.Pipeline.Compiler
