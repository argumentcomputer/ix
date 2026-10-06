/-
  o11a-decline: O11a declines with a recorded cause when the size instance
  its output needs is absent from the input (M1-c; design document §6.3,
  the four obligations of a pass whose output adds a reference;
  `Ix/Compile/Pass/Opt/O11a.lean`).

  Fixture `Tests/Ix/Compile/Pass/O2Split.lean`: the mutual block `SA`/`SB`
  splits (`SA.a : SB → SA`, nothing of `SB` mentions `SA`), so Lean's
  `PassO2.SA._sizeOf_1` (the size function of `SA`, over Lean's block
  recursor) is O11a's pattern: with the switch on, the cross field into the
  lower component `SB` gets its size through `PassO2.SB._sizeOf_inst`.

  Two inputs, each compiled by the Lean pipeline with the switch off and on:

  - **valid neighbour**: the selected closure of `PassO2.SA._sizeOf_1`
    (`Ix.EnvScope.collectSelectedDeps`, which carries the instance). The
    scheduler has the edge `SA._sizeOf_1 → SB._sizeOf_inst`
    (`prepareSizeOfScheduling`, on the input's own condensation); with the
    switch on `SA._sizeOf_1` references `SB._sizeOf_inst` (O11a fired) and
    the compile's non-canonical set is empty;
  - **withheld**: the same closure without `PassO2.SB._sizeOf_inst` and
    without every constant that references it (the `sizeOf_spec` lemmas),
    so the input is closed. No edge to the instance; with the switch on
    `SA._sizeOf_1` keeps O2's relocated form (it references the lower
    component's recursor `PassO2.SB._ix.rec`, not the instance) and the
    non-canonical set is exactly `{PassO2.SA._sizeOf_1}` with a cause that
    names `PassO2.SB._sizeOf_inst`.

  With the switch off nothing is recorded in either input. Every compile
  must have no refusals.

  Run with: `lake test -- --ignored o11a-decline`.
-/
import Ix.EnvScope
import Ix.CompileM
import Ix.CompileDriver
import Tests.Ix.Compile.Pass3

open Lean

namespace Tests.Ix.Compile.O11aDecline

abbrev IxName := _root_.Ix.Name

def ixN (n : Name) : IxName := Tests.Ix.Compile.Pass3.ixN n

/-- `closure` without `drop` and without every constant that references a
dropped one (transitively), so the result is closed. -/
def dropWithDependents (closure : List (Name × ConstantInfo)) (drop : List Name) :
    List (Name × ConstantInfo) := Id.run do
  let mut gone : NameSet := drop.foldl (·.insert ·) {}
  let mut changed := true
  while changed do
    changed := false
    for (n, ci) in closure do
      if gone.contains n then continue
      let mut refs := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then
        refs := refs ++ v.getUsedConstants
      if let .recInfo rv := ci then
        for r in rv.rules do refs := refs ++ r.rhs.getUsedConstants
      if refs.any gone.contains then
        gone := gone.insert n
        changed := true
  return closure.filter fun (n, _) => !gone.contains n

/-- Does the compiled constant `c` reference a constant named `r`? -/
def references (env : Ixon.Env) (c r : Name) : Except String Bool := do
  let some a := env.getAddr? (ixN c) | throw s!"{c} missing from the output"
  let some (k, _) := Tests.Ix.Compile.Pass3.ixonBody env a | throw s!"{c} has no body"
  let names : Std.HashMap Address (Array IxName) := env.named.fold (init := {}) fun m n nd =>
    m.insert nd.addr ((m.getD nd.addr #[]).push n)
  return k.refs.any fun x => (names.getD x #[]).contains (ixN r)

def root : Name := `PassO2.SA._sizeOf_1
def inst : Name := `PassO2.SB._sizeOf_inst
def lowerRec : Name := `PassO2.SB._ix.rec

def run : IO UInt32 := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/O2Split.lean"
  let mut errors : Array String := #[]
  let full := Ix.EnvScope.collectSelectedDeps env [root]
  let withheld := dropWithDependents full [inst]
  let has (cs : List (Name × ConstantInfo)) (n : Name) := cs.any (·.1 == n)
  unless has full inst do errors := errors.push s!"neighbour: the selected closure lacks {inst}"
  if has withheld inst then errors := errors.push s!"withheld: {inst} still present"
  for n in [root, `PassO2.SA, `PassO2.SB, `PassO2.SA.rec] do
    unless has withheld n do errors := errors.push s!"withheld: {n} missing"
  let dropped := full.length - withheld.length
  IO.println s!"[o11a-decline] neighbour {full.length} constants; withheld {withheld.length} \
    ({dropped} dropped: the instance and its dependents)"
  for (label, cs, wantEdge) in [("neighbour", full, true), ("withheld", withheld, false)] do
    -- the scheduling edge, on the input's own condensation
    let phases ← Ix.CompileM.rsCompilePhasesOf cs
    let blocks := Ix.CompileM.prepareSizeOfScheduling phases.rawEnv phases.condensed
    let edge := match blocks.lowLinks.get? (ixN root) with
      | some lo => (blocks.blockRefs.getD lo {}).contains (ixN inst)
      | none => false
    if edge != wantEdge then
      errors := errors.push s!"{label}: scheduling edge {root} → {inst} is \
        {if edge then "present" else "absent"}"
    IO.println s!"[o11a-decline] {label}: scheduling edge {root} → {inst}: {edge}"
    for mode in [false, true] do
      let unit : Tests.Ix.Compile.Pass3.CUnit :=
        { name := s!"o11a-{label}", env, seeds := #[root], closure := cs }
      let out ← Tests.Ix.Compile.Pass3.compileUnit unit mode
      unless out.cenv.ungrounded.isEmpty do
        errors := errors.push s!"{label} mode={mode}: {out.cenv.ungrounded.size} refusals"
      let nc := out.cenv.p3NonCanonical.toList
      IO.println s!"[o11a-decline] {label} mode={mode}: non-canonical set {nc.map fun (n, c) => s!"{n.pretty}: {c}"}"
      let toInst ← IO.ofExcept (references out.env root inst)
      let toLower ← if mode then IO.ofExcept (references out.env root lowerRec) else pure false
      IO.println s!"[o11a-decline] {label} mode={mode}: {root} references {inst}: {toInst}; {lowerRec}: {toLower}"
      if !mode then
        unless nc.isEmpty do errors := errors.push s!"{label} mode=off: records {nc.length} entries"
        if toInst then errors := errors.push s!"{label} mode=off: {root} references {inst}"
      else if wantEdge then
        unless nc.isEmpty do errors := errors.push s!"neighbour: unexpected records {nc.map (·.1.pretty)}"
        unless toInst do errors := errors.push s!"neighbour: O11a did not fire ({root} lacks {inst})"
      else
        match nc with
        | [(n, cause)] =>
          if n != ixN root then errors := errors.push s!"withheld: recorded {n.pretty}, expected {root}"
          unless (cause.splitOn inst.toString).length > 1 do
            errors := errors.push s!"withheld: the cause does not name {inst}: {cause}"
        | _ => errors := errors.push s!"withheld: expected exactly one record ({root}), got {nc.length}"
        if toInst then errors := errors.push s!"withheld: {root} references the absent {inst}"
        unless toLower do errors := errors.push s!"withheld: {root} lacks O2's relocated {lowerRec}"
  for e in errors do IO.println s!"[o11a-decline] FAIL {e}"
  IO.println s!"[o11a-decline] {if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}: \
    2 inputs × 2 switch states"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.O11aDecline
