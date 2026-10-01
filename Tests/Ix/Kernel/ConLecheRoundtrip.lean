/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import LSpec
import Ix.CompileDriver
import Ix.Meta
import Tests.Ix.Kernel.ReaderFidelity
import Tests.Ix.Kernel.EgressFidelity
import Tests.Ix.Kernel.ReaderFidelityDefs

/-! # The Ixon reader's fidelity on compiled Lean declarations (`lake test`)

The Ix.Tc-style roundtrip for con-leche's Ixon reader: the declarations of
`Tests.Ix.Kernel.ReaderFidelityDefs` (nested, mutual, indexed, reflexive and
structure-like inductives, quotients, literals, mutual and well-founded
definitions) and everything in `Init` they reach are compiled with Ix's
compiler, read through `Ix.Kernel.ConLecheReader` as the census reads them,
and compared constant by constant with the reference translation of the Lean
constants (`Tests.Ix.Kernel.ReaderFidelity`, whose docstring lists the
normalizations and canonicalizations it classifies).

The suite fails on any unexplained difference, on any name, shape-data or
pin-table problem, and unless each fixture declaration has its expected
verdict. Tamper tests check that the comparison has teeth: a reader entry
altered in its value, a level name, a binder annotation, a literal, a rule
constructor or a constructor count is never judged equal.

The same compiled closure checks the kernel's output side
(`Tests.Ix.Kernel.EgressFidelity`): every block's projection records as the
certified writer writes them against the compiler's, every inductive and
definition block's order, and over two accepted batches the reader's
declarations with written projections and the installed environments of
`ConLecheAdmission.checkConstants`, `Projection.checkBytes` and
`BlockOrder.checkBytes`, with every projection record naming an installed
constant of its kind.

The whole of `Init` and `Std` runs through the same comparisons (projections and
block order only, for the output side) in `kernel-reader-fidelity`. -/

namespace Tests.Ix.Kernel.ConLecheRoundtrip

open LSpec
open Tests.Ix.Kernel.ReaderFidelity

def defsModule : Lean.Name := `Tests.Ix.Kernel.ReaderFidelityDefs

def defs (n : String) : Lean.Name := defsModule ++ n.toName

/-- The compiled closure of the fixture module's own declarations. -/
def input : IO (Lean.Environment × Input) := do
  let leanEnv ← getCompileEnv #[defsModule]
  let some idx := leanEnv.getModuleIdx? defsModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    if leanEnv.getModuleIdxFor? n == some idx then some n else none
  -- the Ixon prelude's constants, so that their records carry metadata
  let prelude := #[`Eq, `Nat, `PUnit, `Empty, `False, `Quot, `Quot.mk, `Quot.lift, `Quot.ind,
    `Quot.sound, `And, `Bool]
  let closed ← IO.ofExcept (closure leanEnv (seeds ++ prelude))
  let compiled ← match ← Ix.CompileM.compileLeanConsts closed (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compilation failed: {e}")
  unless compiled.ungroundedCount == 0 do
    throw (IO.userError s!"{compiled.ungroundedCount} constants are ungrounded")
  let ixon ← IO.ofExcept (Ixon.deEnv compiled.bytes)
  return (leanEnv, ← Input.ofEnv leanEnv ixon)

/-- The verdict each fixture declaration must get. -/
def expected : List (Lean.Name × Verdict) := [
  -- inductives: members, constructors, recursors
  (defs "Color", .equal), (defs "Color.red", .equal), (defs "Color.rec", .equal),
  (defs "Point", .equal), (defs "Point.mk", .equal), (defs "Point.rec", .equal),
  (defs "Point.x", .equal), (defs "Point3", .equal), (defs "Point3.z", .equal),
  (defs "Point3.toPoint", .equal),
  (defs "Vec", .equal), (defs "Vec.cons", .equal), (defs "Vec.rec", .equal),
  (defs "WTree", .equal), (defs "WTree.sup", .equal), (defs "WTree.rec", .equal),
  (defs "Rose", .equal), (defs "Rose.node", .equal), (defs "Rose.rec", .equal),
  (defs "Rose.rec_1", .equal),
  (defs "ATree", .equal), (defs "ATree.node", .equal), (defs "ATree.rec_1", .equal),
  (defs "ATree.rec_2", .equal),
  (defs "Node", .equal), (defs "Node.mk", .equal), (defs "Node.rec", .equal),
  (defs "Node.val", .normalized "projection rewrite"),
  (defs "Node.kids", .normalized "projection rewrite"),
  (defs "Even", .equal), (defs "Odd", .equal), (defs "Odd.succ", .equal),
  (defs "Even.rec", .canonicalized "auxiliary regenerated"),
  -- a mutual block of data types: the compiler regenerates its recursors in
  -- canonical member order, and the definitions over it call them through
  -- permuted call sites
  (defs "Tm", .equal), (defs "Args.cons", .equal),
  (defs "Tm.rec", .canonicalized "auxiliary regenerated"),
  (defs "Args.rec", .canonicalized "auxiliary regenerated"),
  (defs "Tm.size", .canonicalized "call-site surgery"),
  (defs "Trivial", .equal), (defs "Trivial.rec", .equal),
  (defs "Both", .equal), (defs "Both.left", .equal),
  (defs "Pair", .equal), (defs "Pair.mk", .equal),
  -- definitions, theorems, opaques, axioms
  (defs "twice", .equal), (defs "NatPair", .equal), (defs "sumPoint", .equal),
  (defs "Vec.length", .equal), (defs "Rose.size", .equal), (defs "Rose.size.sizes", .equal),
  (defs "isEven", .equal), (defs "isOdd", .equal),
  (defs "log2", .equal), (defs "WTree.depthAt", .equal),
  (defs "ParityQ", .equal), (defs "ParityQ.toBool", .equal), (defs "ParityQ.toBool_mk", .equal),
  (defs "smallNat", .equal), (defs "bigNat", .equal), (defs "greeting", .equal),
  (defs "letter", .equal), (defs "bigNat_pos", .equal),
  (defs "twice_id", .equal), (defs "isEven_two", .equal), (defs "even_two", .equal),
  (defs "secret", .equal), (defs "fidelityAxiom", .equal),
  (defs "levelImax", .equal),
  -- alpha-equivalent to another definition: one address, the compiler's
  -- min-merged hint
  (defs "levelMax", .normalized "compiler hint (per address)"),
  -- declined by the reader
  (defs "spin._unsafe_rec", .declined "partial definition"),
  (defs "unsafeId", .declined "unsafe definition"),
  -- the prelude and the pinned constants
  (`Quot, .equal), (`Quot.lift, .equal), (`Quot.mk, .equal), (`Quot.ind, .equal),
  (`Quot.sound, .equal), (`Eq, .equal), (`Eq.rec, .equal), (`Nat, .equal), (`Nat.rec, .equal),
  (`Nat.add, .equal), (`String.ofList, .equal), (`Char.ofNat, .equal), (`List.cons, .equal) ]

/-! ## Tampering: the comparison has teeth -/

def always : ConLeche.BinderMeta := ⟨.ifAllZero []⟩

/-- The first binder's annotation set to `always`. -/
def tamperPw : ConLeche.Expr → Option ConLeche.Expr
  | .lam t b _ => some (.lam t b always)
  | .forallE t b _ => some (.forallE t b always)
  | _ => none

/-- A natural-number literal bumped. -/
partial def tamperLit : ConLeche.Expr → Option ConLeche.Expr
  | .lit (.natVal n) => some (.lit (.natVal (n + 1)))
  | .app f a => ((tamperLit a).map (.app f ·)).orElse fun _ => (tamperLit f).map (.app · a)
  | .lam t b m => (tamperLit b).map (.lam t · m)
  | _ => none

/-- Each tamper: its label, the Lean name whose pair it alters, the alteration. -/
def tampers : List (String × Lean.Name × (Entry → Option Entry)) := [
  ("definition value replaced by its type", defs "twice", fun
    | .defn cv _ h => some (.defn cv cv.type h) | _ => none),
  ("level parameter renamed", defs "twice", fun
    | .defn cv v h => some (.defn { cv with levelParams := cv.levelParams.map (·.str "x") } v h)
    | _ => none),
  ("binder annotation set", defs "twice", fun
    | .defn cv v h => (tamperPw v).map (.defn cv · h) | _ => none),
  ("definition hint changed", defs "twice", fun
    | .defn cv v _ => some (.defn cv v .opaque) | _ => none),
  ("literal changed", defs "smallNat", fun
    | .defn cv v h => (tamperLit v).map (.defn cv · h) | _ => none),
  ("recursor rules reversed", defs "Color.rec", fun
    | .recr cv m r rs => some (.recr cv m r rs.reverse) | _ => none),
  ("recursor rule dropped", defs "Color.rec", fun
    | .recr cv m r rs => some (.recr cv m r rs.tail) | _ => none),
  ("constructor field count bumped", defs "Point.mk", fun
    | .ctor cv p f => some (.ctor cv p (f + 1)) | _ => none),
  ("inductive parameter count bumped", defs "Point", fun
    | .induct cv p => some (.induct cv (p + 1)) | _ => none),
  ("theorem read as an axiom", defs "twice_id", fun
    | .thm cv _ => some (.axiom cv) | _ => none) ]

/-- The tampers the comparison does not catch (an empty list passes). -/
def uncaught (report : Report) : List String :=
  tampers.filterMap fun (label, n, f) =>
    match report.pairs[n]? with
    | some (actual, expected) =>
      match f actual with
      | some altered => if (entryDiff altered expected).isSome then none else some label
      | none => some s!"{label} (does not apply to {n})"
    | none => some s!"{label} ({n} was not compared)"

/-- The reader-fidelity checks of the fixture closure: the report and every
failure (an expected verdict missed, an unexplained difference, a problem,
an uncaught tamper). -/
def evaluateReader (inp : Input) : IO (Report × Array String) := do
  let watched : Std.HashSet Lean.Name := (expected.map (·.1) ++ tampers.map (·.2.1)).foldl
    (·.insert ·) {}
  let report ← run inp (keep := watched.contains)
  let mut errors : Array String := #[]
  for (n, v) in expected do
    match report.verdicts[n]? with
    | some got => unless got == v do errors := errors.push s!"{n}: {got.label}, expected {v.label}"
    | none => errors := errors.push s!"{n}: not compared"
  unless report.unexplained.isEmpty do
    errors := errors.push s!"{report.unexplained.size} unexplained differences"
  unless report.problems.isEmpty do
    errors := errors.push s!"{report.problems.size} problems"
  unless report.unmatched.isEmpty do
    errors := errors.push s!"{report.unmatched.size} reader constants without a Lean constant"
  unless report.projRewrites > 0 && report.generated > 0 do
    errors := errors.push "no projection rewrite or generated record was exercised"
  -- the tampers run against the kept pairs
  for t in uncaught report do errors := errors.push s!"tamper not caught: {t}"
  return (report, errors)

/-- The two batches of the entry checks: blocks nested through containers,
mutual blocks and a nested structure (some of whose recursor blocks the
block-order entry refuses: `Tests.Ix.Kernel.EgressFidelity`, "Block order"),
and declarations without such blocks, which all three certified entries must
accept with the same environment. -/
def nestedSeeds : Array Lean.Name :=
  #[defs "Node", defs "Rose.size", defs "Tm.size", defs "ATree"]

def plainSeeds : Array Lean.Name :=
  #[defs "twice_id", defs "Point3", defs "Vec.length", defs "ParityQ.toBool_mk", defs "greeting",
    defs "bigNat_pos", defs "isEven_two", defs "even_two", defs "levelImax", defs "WTree.depthAt"]

/-- The egress checks of the fixture closure (`Tests.Ix.Kernel.EgressFidelity`):
every block's projections as the certified writer writes them and its order,
and, over two batches the checker accepts, re-reading with written
projections and the certified entries' installed environments. The report
lines and every failure. -/
def evaluateEgress (inp : Input) : IO (Array String × Array String) := do
  let proj := EgressFidelity.projections inp.store (inp.ixon.blobs.toList)
  let nested ← EgressFidelity.entries inp (← EgressFidelity.acceptedClosure inp nestedSeeds)
  let plain ← EgressFidelity.entries inp (← EgressFidelity.acceptedClosure inp plainSeeds)
  let mut errors : Array String := #[]
  unless proj.problems.isEmpty do errors := errors.push s!"{proj.problems.size} projection problems"
  unless proj.compiled > 0 && proj.matched == proj.compiled do
    errors := errors.push s!"{proj.matched} of {proj.compiled} projection records written"
  for p in proj.orderProblems do errors := errors.push s!"block order: {p}"
  for (label, ent) in [("nested", nested), ("plain", plain)] do
    unless ent.problems.isEmpty do errors := errors.push s!"{label}: {ent.problems.size} entry problems"
    unless ent.projectionRecords > 0 && ent.projectionsInstalled == ent.projectionRecords do
      errors := errors.push s!"{label}: {ent.projectionsInstalled} of {ent.projectionRecords} projections installed"
  if plain.blockOrderRefusal.isSome then
    errors := errors.push "plain: the block-order entry refused the batch"
  let refused := (proj.refused.getD "recursor" #[]).toList.map fun a =>
    s!"{a} {EgressFidelity.memberNames inp.ixon inp.store a}"
  return (#[proj.summary, s!"refused recursor blocks: {refused}", s!"nested {nested.summary}",
    s!"plain {plain.summary}"], errors)

/-- Compile the fixture closure once and run both evaluations. -/
def evaluate : IO (Report × Array String × Array String) := do
  let (_, inp) ← input
  let (report, readerErrors) ← evaluateReader inp
  let (lines, egressErrors) ← evaluateEgress inp
  return (report, lines, readerErrors ++ egressErrors)

def suiteIO : TestSeq :=
  .individualIO "reader fidelity and egress: compiled fixture closure against Lean" none (do
    let (report, lines, errors) ← evaluate
    IO.println report.summary
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, report.constants, 0, msg)) .done

def suite : List TestSeq := [suiteIO]

end Tests.Ix.Kernel.ConLecheRoundtrip
