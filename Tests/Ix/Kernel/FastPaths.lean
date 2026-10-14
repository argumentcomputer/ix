import LSpec
import Ix.Meta
import Ix.CompileDriver
import Ix.KernelCheck
import Ix.Tc
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.Kernel.FastPathDefs

/-! # Reductions beyond Lean's, per kernel (`kernel-fast-paths`)

Each probe of `Tests.Ix.Kernel.FastPathDefs` is checked with its whole
dependency closure (recursors included), compiled once by Ix's compiler, by
three kernels:

* the Rust kernel (`rsCheckConstsFFI`, every closure member by name);
* `Ix.Tc` (`checkIxeBytesAnon` on the compiled bytes);
* IxC, through the environment check (`SourceIngressCompare.ixonVerdicts`:
  the verified fold one record at a time, at the committed `Nat`-operation
  pins).

A probe expected to be rejected names its culprit: the false or
non-definitional equation itself, or, for a derivation of `False`, the
equation it uses. Every kernel must reject the culprit, and nothing else in
the closure may fail except the probe itself when it is a derivation (the
Rust kernel and `Ix.Tc` check it with its dependencies trusted and accept
it; IxC blocks it behind the culprit). A probe expected to be accepted must
have every closure member accepted. So the test fails both when a kernel
accepts a proof of `False` and when a removed fast path's honest
replacement stops reducing the canonical forms. -/

namespace Tests.Ix.Kernel.FastPaths

open LSpec

def defs (n : String) : Lean.Name := `Tests.Ix.Kernel.FastPathDefs ++ n.toName

inductive Expect where
  | accept
  | reject (culprit : Lean.Name)

structure Probe where
  name : Lean.Name
  expect : Expect

def probes : List Probe :=
  let rejectSelf (n : String) : Probe := ⟨defs n, .reject (defs n)⟩
  let accept (n : String) : Probe := ⟨defs n, .accept⟩
  [ -- the false equations (two spellings of the `LT` one), and the two
    -- conversions Lean does not make
    rejectSelf "badLt", rejectSelf "badLtOfNat", rejectSelf "badOfNat",
    rejectSelf "badSizeOf",
    rejectSelf "numBits64", rejectSelf "finCommute",
    -- the derivations of `False`
    ⟨defs "falseLt", .reject (defs "badLt")⟩,
    ⟨defs "falseLtOfNat", .reject (defs "badLtOfNat")⟩,
    ⟨defs "falseOfNat", .reject (defs "badOfNat")⟩,
    ⟨defs "falseSizeOf", .reject (defs "badSizeOf")⟩,
    -- the controls
    accept "okLt", accept "okOfNat", accept "okSizeOf",
    accept "weirdLtVal", accept "weirdOfNatVal", accept "weirdSizeOfVal",
    accept "okUlt", accept "okSizeOfVar", accept "okSizeOfPUnitVar", accept "okFinRec" ]

/-- One kernel's verdict on one constant. -/
inductive Verdict where
  | accept
  | reject (reason : String)
  /-- not checked: it depends on the rejected constant `root` -/
  | blocked (root : String)
  deriving Inhabited

def Verdict.isAccept : Verdict → Bool
  | .accept => true
  | _ => false

def Verdict.isReject : Verdict → Bool
  | .reject _ => true
  | _ => false

def Verdict.label : Verdict → String
  | .accept => "accept"
  | .reject r => s!"reject ({(r.take 120).toString})"
  | .blocked r => s!"blocked behind {r}"

abbrev Verdicts := Std.HashMap Lean.Name Verdict

/-- The Rust kernel: every name checked, its dependencies trusted. -/
def rustVerdicts (closed : List (Lean.Name × Lean.ConstantInfo)) : IO Verdicts := do
  let names := (closed.map (·.1)).toArray
  let results ← Ix.KernelCheck.rsCheckConstsFFI closed names
    (Array.replicate names.size true) true
  let mut out : Verdicts := {}
  for i in [:names.size] do
    out := out.insert names[i]! <| match results[i]! with
      | none => .accept
      | some e => .reject e.message
  return out

/-- `Ix.Tc` on the compiled bytes, per address, read back by name. -/
def tcVerdicts (compiled : Ix.CompileM.LeanPipelineOut) (names : List Lean.Name) :
    IO Verdicts := do
  let results ← IO.ofExcept (Ix.Tc.checkIxeBytesAnon compiled.bytes |>.mapError (s!"Ix.Tc: {·}"))
  let byAddr : Std.HashMap Address (Option String) :=
    results.foldl (init := {}) fun m r => m.insert r.addr r.err?
  let mut out : Verdicts := {}
  for n in names do
    let some named := compiled.env.named[Ix.Name.fromLeanName n]? | continue
    if let some err? := byAddr[named.addr]? then
      out := out.insert n <| match err? with
        | none => .accept
        | some e => .reject e
  return out

/-- IxC's environment check on the compiled environment, by name. -/
def ixcVerdicts (compiled : Ix.CompileM.LeanPipelineOut) (names : List Lean.Name) :
    IO Verdicts := do
  let natPins ← IO.ofExcept Ix.Kernel.Reader.builtinNatOpPins
  let rows ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts compiled.env natPins
  let mut out : Verdicts := {}
  for n in names do
    if let some (outcome, reason) := rows[Ix.LeanIngress.ingressName (Ix.Name.fromLeanName n)]? then
      out := out.insert n <| match outcome with
        | "accept" => .accept
        | "blocked" => .blocked reason
        | _ => .reject s!"{outcome}: {reason}"
  return out

/-- The check of one probe against one kernel's verdicts. -/
def checkProbe (kernel : String) (closure : List Lean.Name) (verdicts : Verdicts)
    (p : Probe) : TestSeq :=
  let missing := closure.filter (!verdicts.contains ·)
  let failures := closure.filter fun n => !(verdicts.getD n .accept).isAccept
  let describe (ns : List Lean.Name) : String :=
    ", ".intercalate (ns.map fun n => s!"{n}: {(verdicts.getD n .accept).label}")
  let complete := test s!"{kernel}: every member of {p.name}'s closure has a verdict \
    (missing: {missing.take 5})" missing.isEmpty
  match p.expect with
  | .accept =>
    complete ++ test s!"{kernel} accepts the closure of {p.name} ({describe failures})"
      failures.isEmpty
  | .reject culprit =>
    let culpritRejected := (verdicts.getD culprit .accept).isReject
    -- the probe itself, when it is a derivation: accepted (dependencies
    -- trusted) or blocked behind the culprit, never rejected on its own
    let probeOk := p.name == culprit || !(verdicts.getD p.name .accept).isReject
    let others := failures.filter fun n => n != culprit && n != p.name
    complete
      ++ test s!"{kernel} rejects {culprit}, so the closure of {p.name} \
          ({(verdicts.getD culprit .accept).label})" culpritRejected
      ++ test s!"{kernel}: {p.name} fails only through {culprit} ({describe others})"
          (probeOk && others.isEmpty)

def run : IO UInt32 := do
  let leanEnv ← get_env!
  let mut closures : Std.HashMap Lean.Name (List Lean.Name) := {}
  let mut union : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for p in probes do
    let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[p.name])
    closures := closures.insert p.name (closed.map (·.1))
    for (n, ci) in closed do union := union.insert n ci
  let closed := union.toList
  let names := closed.map (·.1)
  IO.println s!"[kernel-fast-paths] {probes.length} probes, {closed.length} constants in their closures"
  let t0 ← IO.monoMsNow
  let compiled ← match ← Ix.CompileM.compileLeanConsts closed (numWorkers := 4) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compilation failed: {e}")
  unless compiled.ungroundedCount == 0 do
    throw (IO.userError s!"{compiled.ungroundedCount} constants are ungrounded")
  let t1 ← IO.monoMsNow
  let rust ← rustVerdicts closed
  let t2 ← IO.monoMsNow
  let tc ← tcVerdicts compiled names
  let t3 ← IO.monoMsNow
  let ixc ← ixcVerdicts compiled names
  let t4 ← IO.monoMsNow
  IO.println s!"[kernel-fast-paths] compile {t1 - t0} ms, Rust {t2 - t1} ms, \
    Ix.Tc {t3 - t2} ms, IxC {t4 - t3} ms"
  let mut seq : TestSeq := .done
  for (kernel, verdicts) in [("Rust", rust), ("Ix.Tc", tc), ("IxC", ixc)] do
    for p in probes do
      seq := seq ++ checkProbe kernel (closures.getD p.name []) verdicts p
  lspecIO (.ofList [("kernel-fast-paths", [seq])]) []

end Tests.Ix.Kernel.FastPaths
