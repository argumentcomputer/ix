import IxCCTests.Pipeline.Support
import IxCCTests.Rt.Differential
import IxCCTests.Rt.Cases
import IxCCTests.Lam.Differential
import IxCC.CompileClaim

/-! The compiler: the `ixcc` command line on the fixtures,
`produce` + `Recheck.run` against the stage suites' pipelines, the
certificate's serialisation, and the declines.

* **The command line** (`IxCC.Cli.main`, in process, or the built
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
  `Alloc.run`, `Backend.emit`; `IxCCTests.Rt.Machine.compile`).
* **Round trips**: the certificate's JSON parses back to a certificate with
  the same JSON, and `run` on it makes the same object.
* **Declines**: the fallback route (a sidecar without equations) is
  declined at `fir` with `fir.closures`; a root with six parameters with
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
    "--no-typecheck", "--rc", "auto", "-o", gcdAutoObj.toString, "--emit-cert", gcdAutoCert.toString]
  expectEq a code 0 "gcd --rc auto: compile exit code"
  expect a ((← IO.FS.readBinFile gcdAutoObj) == (← IO.FS.readBinFile gcdOffObj))
    "gcd --rc auto: object differs from --rc off"
  let gcdAutoCertText := (← IO.FS.readFile gcdAutoCert).trimAscii.toString
  expect a (!gcdAutoCertText.startsWith "[\"ixcc/rc-cert/2\"")
    "gcd --rc auto: scalar closure should emit ixcc/cert/1"
  let gcdOnObj := t.work / "gcd.rc-on.o"
  let gcdOnCert := t.work / "gcd.rc-on.cert.json"
  let code ← cli t ["compile", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--no-typecheck", "--rc", "on", "-o", gcdOnObj.toString, "--emit-cert", gcdOnCert.toString]
  expectEq a code 0 "gcd --rc on: compile exit code"
  let gcdOnCertText := (← IO.FS.readFile gcdOnCert).trimAscii.toString
  expect a (gcdOnCertText.startsWith "[\"ixcc/rc-cert/2\"")
    "gcd --rc on: should emit ixcc/rc-cert/2"
  let code ← cli t ["check-cert", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--no-typecheck", "--cert", gcdOnCert.toString]
  expectEq a code 0 "gcd --rc on: check-cert exit code"
  let gcdFromRcCertObj := t.work / "gcd.from-rc-cert.o"
  let code ← cli t ["compile", gcdIxe, "--equations", gcdEqs, "--root", "entry",
    "--no-typecheck", "--cert", gcdOnCert.toString, "-o", gcdFromRcCertObj.toString]
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
    "--no-typecheck", "--rc", "auto", "-o", revAutoObj.toString, "--emit-cert", revAutoCert.toString]
  expectEq a code 0 "reverseList --rc auto: compile exit code"
  let revAutoCertText := (← IO.FS.readFile revAutoCert).trimAscii.toString
  expect a (revAutoCertText.startsWith "[\"ixcc/rc-cert/2\"")
    "reverseList --rc auto: heap closure should emit ixcc/rc-cert/2"
  let revOnObj := t.work / "reverseList.rc-on.o"
  let revOnCert := t.work / "reverseList.rc-on.cert.json"
  let code ← cli t ["compile", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--no-typecheck", "--rc", "on", "-o", revOnObj.toString, "--emit-cert", revOnCert.toString]
  expectEq a code 0 "reverseList --rc on: compile exit code"
  expect a ((← IO.FS.readBinFile revAutoObj) == (← IO.FS.readBinFile revOnObj))
    "reverseList: --rc auto and --rc on objects differ"
  expectEq a revAutoCertText ((← IO.FS.readFile revOnCert).trimAscii.toString)
    "reverseList: --rc auto and --rc on certificates differ"
  let code ← cli t ["check-cert", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--no-typecheck", "--cert", revAutoCert.toString]
  expectEq a code 0 "reverseList --rc auto: check-cert exit code"
  let revFromCertObj := t.work / "reverseList.from-rc-cert.o"
  let code ← cli t ["compile", rcIxe, "--equations", rcEqs, "--root", rcRoot,
    "--no-typecheck", "--cert", revAutoCert.toString, "-o", revFromCertObj.toString]
  expectEq a code 0 "reverseList --rc auto: compile --cert exit code"
  expect a ((← IO.FS.readBinFile revFromCertObj) == (← IO.FS.readBinFile revAutoObj))
    "reverseList --rc auto: compile --cert wrote a different object"
  return #["--rc auto/on: gcd selects zeroRc (ixcc/cert/1), reverseList selects plainRc (ixcc/rc-cert/2); check-cert and compile --cert agree"]

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
  out := out ++ (← rcCommandLine a t)
  return out

/-! ## The object the stage suites make -/

private def setPiContracts : List Ixon.V3.BinderContract → Src.Term → Src.Term
  | c :: cs, .pi b r d body => .pi { b with contract := c } r d (setPiContracts cs body)
  | _, t => t

private def setLamContracts : List Ixon.V3.BinderContract → Src.Term → Src.Term
  | c :: cs, .lam b d body => .lam { b with contract := c } d (setLamContracts cs body)
  | _, t => t

/-- Attach frontend binder contracts (`1` linear on `build`, `!` unique on `revAcc`,
`~` local borrow on `sumL`) and a matching `Src.Resource.Context` to the `OS16-plain`
heap closure (`build` + `revAcc` + `sumL`), then verify that it passes `Recheck.produce`,
`Recheck.run`, `Recheck.runWithContracts`, `Recheck.compileInputWithContracts`, and
`RcReplay.produceAuto` on the `.zeroRc` path. -/
def contractZeroRc (a : Assert) : IO String := do
  let ixe : FilePath := "fixtures/ownership/OS16-plain.ixe"
  let eqs : FilePath := "fixtures/ownership/OS16-plain.equations.json"
  let baseInp ← ingressFile ixe eqs ["entry"] (typecheck := false)
  let p0 := baseInp.program
  let cLinear : Ixon.V3.BinderContract := { uses := .linear }
  let cUnique : Ixon.V3.BinderContract := { value := { owned := .unique } }
  let cBorrow : Ixon.V3.BinderContract := { value := { locality := .local } }
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
  let specs : List (Src.CId × Src.CId × List Ixon.V3.BinderContract) :=
    [(buildId, buildEqId, [cLinear, cLinear]),
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
  let eqAddr ← match p0.known.eq with
    | some eqId => pure (p0.addr eqId)
    | none => throw (IO.userError "OS16: missing pinned Eq")
  let eqPairs : Array (Ixon.Address × Ixon.Address) :=
    specs.toArray.map fun (f, thm, _) => (p0.addr f, p0.addr thm)
  let profile : Src.Resource.Profile := { eqType := some eqAddr, equations := eqPairs }
  let profBytes := profile.bytes
  let profAddr := Ixon.Address.blake3Pure profBytes
  let checkedPairs : List Src.Resource.Pair :=
    specs.filterMap fun (f, thm, _) =>
      match consts.get? f with
      | some entry => some
        { definition := p0.addr f
          equation := p0.addr thm
          profile := profAddr
          contracts := Src.Resource.headers entry.decl.type }
      | none => none
  let ctx : Src.Resource.Context :=
    { address := profAddr, bytes := profBytes, pairs := checkedPairs }
  let annotatedProg : Src.Program := { p0 with consts, resource := some ctx }
  let annotatedInp : Input := { baseInp with program := annotatedProg }
  let cfg := Config.forInput { names := ["entry"], provenance := some Rt.Machine.testProvenance } annotatedInp
  let cert ← ofErr "OS16-contract produce" fun _ => produce cfg annotatedInp
  let art ← ofErr "OS16-contract run" fun _ => run cfg annotatedProg cert
  let artWithContracts ← ofErr "OS16-contract runWithContracts" fun _ =>
    runWithContracts cfg annotatedProg cert
  let (cert2, art2) ← ofErr "OS16-contract compileInputWithContracts" fun _ =>
    compileInputWithContracts { names := ["entry"], provenance := some Rt.Machine.testProvenance } annotatedInp
  expect a (artWithContracts.object == art.object && art2.object == art.object && cert2.toText == cert.toText)
    "OS16-contract: runWithContracts and compileInputWithContracts agree with produce + run"
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
  let autoRes ← ofErr "OS16-contract produceAuto" fun _ =>
    RcReplay.produceAuto { names := ["entry"], provenance := some Rt.Machine.testProvenance } annotatedInp
  match autoRes with
  | .zeroRc autoCert autoArt _ =>
    expect a (autoCert.toText == cert.toText && autoArt.object == art.object)
      "OS16-contract: produceAuto zeroRc certificate and object must match produce + run"
  | .plainRc .. | .immortal .. =>
    expect a false "OS16-contract: produceAuto did not select zeroRc"
  let (osClaim, osCertText, osElf) ← ofErr "OS16-contract CompileClaim.produce" fun _ =>
    CompileClaim.produce cfg annotatedInp
  expect a (osClaim.policy == .zeroRc && osClaim.abiArity == 1 && osElf == art.object && osCertText == cert.toText)
    "OS16-contract: CompileClaim.produce metadata and ELF match"
  expect a (CompileClaim.verifyProgram cfg annotatedProg osClaim osCertText)
    "OS16-contract: CompileClaim.verifyProgram must accept valid zeroRc claim"
  let badAddr := Ixon.Address.blake3Pure (ByteArray.mk #[0xde, 0xad, 0xbe, 0xef])
  expect a (!CompileClaim.verifyProgram cfg annotatedProg { osClaim with elfHash := badAddr } osCertText)
    "OS16-contract: CompileClaim.verifyProgram must reject tampered elfHash"
  expect a (!CompileClaim.verifyProgram cfg annotatedProg { osClaim with target := badAddr } osCertText)
    "OS16-contract: CompileClaim.verifyProgram must reject tampered target"
  expect a (!CompileClaim.verifyProgram cfg annotatedProg { osClaim with abiArity := osClaim.abiArity + 1 } osCertText)
    "OS16-contract: CompileClaim.verifyProgram must reject tampered abiArity"
  pure s!"OS16-contract: heap closure with 1/!/~ contracts passes produce + run + runWithContracts + CompileClaim.verifyProgram on zeroRc ({art.object.size} bytes)"

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
  let rcInp ← ingressFile rcIxe rcEqs [rcRoot] (typecheck := false)
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
  expect a (gcdClaimBytes.size == 103 && gcdClaim.roleTable == none &&
      gcdClaimBytes.get! 0 == 0xE8 && gcdClaimBytes.get! 1 == 0x05 &&
      gcdClaimBytes.get! 2 == 0x04 && gcdClaimBytes.get! 3 == 0x07 &&
      gcdClaimBytes.get! 36 == 0 && gcdClaimBytes.get! 69 == 1 && gcdClaimBytes.get! 70 == 2 &&
      CompileClaim.ofClaimBytes gcdClaimBytes == some gcdClaim &&
      CompileClaim.ofPayloadBytes gcdClaim.toPayloadBytes == some gcdClaim &&
      gcdClaim.commit == Ixon.Address.blake3Pure gcdClaimBytes)
    "gcd CompileClaim: wire envelope layout (#[0xE8, 0x05, 0x04, 0x07, ...], no role table), roundtrip, and deterministic BLAKE3 commit"
  let rcClaimBytes := rcClaim.toClaimBytes
  expect a (rcClaimBytes.size == 103 &&
      rcClaimBytes.get! 0 == 0xE8 && rcClaimBytes.get! 1 == 0x05 &&
      rcClaimBytes.get! 2 == 0x04 && rcClaimBytes.get! 3 == 0x07 &&
      rcClaimBytes.get! 36 == 0 && rcClaimBytes.get! 69 == 2 && rcClaimBytes.get! 70 == 2 &&
      CompileClaim.ofClaimBytes rcClaimBytes == some rcClaim &&
      CompileClaim.ofPayloadBytes rcClaim.toPayloadBytes == some rcClaim &&
      rcClaim.commit == Ixon.Address.blake3Pure rcClaimBytes &&
      rcClaim.commit != gcdClaim.commit)
    "reverseList CompileClaim: wire envelope layout (#[0xE8, 0x05, 0x04, 0x07, ...], no role table), roundtrip, and deterministic BLAKE3 commit"
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
  let l ← IO.ofExcept ((IxCC.Rt.lower {} (wide 6)).mapError (·.render))
  match l.compile Rt.Machine.testProvenance with
  | .error (.stacking (.export ..)) => expect a true ""
  | .error e => expect a false s!"six parameters without the check: {e}"
  | .ok _ => expect a false "six parameters without the check: the backend accepted it"
  out := out.push "  (without the check, stacking rejects the six-parameter wrapper: stacking.export)"
  -- names, certificates
  out := out.push (← expectErr a "unknown root" (ingress bytes json ["K1.nope"] false) .cli "cli.root")
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

/-! ## Reports -/

/-- The command line's parser, its IR dumps, statistics and signatures
(the parts `compile` prints). -/
def reports (a : Assert) : IO (Array String) := do
  let base := ["compile", "c.ixe", "--equations", "e.json", "-o", "o.o"]
  match IxCC.Cli.parse (base ++ ["--root", "A", "--root", "B", "--dump-ir", "all", "--stats"]) with
  | .ok o => expect a (o.roots == ["A", "B"] && o.dumps == IxCC.Cli.dumpLevels && o.stats && o.rc == .off) "parse"
  | .error e => expect a false s!"parse: {e}"
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
