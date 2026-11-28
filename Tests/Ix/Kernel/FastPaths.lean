import LSpec
import Ix.Meta
import Ix.CompileCertified
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.Kernel.FastPathDefs

/-! # Reductions beyond Lean's, per kernel (`kernel-fast-paths`)

Each probe of `Tests.Ix.Kernel.FastPathDefs` is checked with its whole
dependency closure (recursors included) by IxCK on the Lean compiler's
output, through the environment check (`SourceIngressCompare.ixonVerdicts`:
the verified fold one record at a time, under the default role table and
its evidence).

A probe expected to be rejected names its culprit: the false or
non-definitional equation itself, or, for a derivation of `False`, the
equation it uses. The kernel must reject the culprit, and nothing else in
the closure may fail except the probe itself when it is a derivation
(accepted with its dependencies trusted, or, as IxCK does, blocked behind
the culprit; never rejected on its own). A probe expected to be accepted must
have every closure member accepted. So the test fails both when IxCK
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

/-- IxCK's environment check on the compiled environment, by name. -/
def ixcVerdicts (compiled : Ix.CompileM.CertifiedOut) (names : List Lean.Name) :
    IO Verdicts := do
  let rows ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts compiled.env
  let mut out : Verdicts := {}
  for n in names do
    if let some (outcome, reason) := rows[Ix.LeanIngress.ingressKey (Ix.Name.fromLeanName n)]? then
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
  let compiled ← match ← Ix.CompileM.compileCertified leanEnv closed 4 with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compilation failed: {e}")
  unless compiled.failures.isEmpty do
    throw (IO.userError s!"{compiled.failures.toMap.size} constants are ungrounded")
  let t1 ← IO.monoMsNow
  let ixc ← ixcVerdicts compiled names
  let t2 ← IO.monoMsNow
  IO.println s!"[kernel-fast-paths] compile {t1 - t0} ms, IxCK {t2 - t1} ms"
  let mut seq : TestSeq := .done
  for (kernel, verdicts) in [("IxCK", ixc)] do
    for p in probes do
      seq := seq ++ checkProbe kernel (closures.getD p.name []) verdicts p
  lspecIO (.ofList [("kernel-fast-paths", [seq])]) []

end Tests.Ix.Kernel.FastPaths
