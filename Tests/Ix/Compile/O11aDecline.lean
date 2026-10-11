/-
  o11a-decline: O11a declines with a recorded cause when the size instance
  its output needs is absent from the input (M1-c; design document §6.3,
  the four obligations of a pass whose output adds a reference;
  `Ix/Compile/Pass/Opt/O11a.lean`).

  Fixture `Tests/Ix/Compile/Pass/O2Split.lean`: the mutual block `SA`/`SB`
  splits (`SA.a : SB → SA`, nothing of `SB` mentions `SA`), so Lean's
  `PassO2.SA._sizeOf_1` (the size function of `SA`, over Lean's block
  recursor) is O11a's pattern: under Pass 3, the cross field into the
  lower component `SB` gets its size through `PassO2.SB._sizeOf_inst`.

  Two inputs, each compiled by the Lean pipeline (Pass 3, the only mode since
  M6R slice 6; until then also with the legacy surgery, `IX_PASS3=off`, where
  nothing was recorded):

  - **valid neighbour**: the selected closure of `PassO2.SA._sizeOf_1`
    (`Ix.EnvScope.collectSelectedDeps`, which carries the instance). The
    scheduler has the edge `SA._sizeOf_1 → SB._sizeOf_inst`
    (`prepareSizeOfScheduling`, on the input's own condensation);
    `SA._sizeOf_1` references `SB._sizeOf_inst` (O11a fired) and
    the compile's non-canonical set is empty;
  - **withheld**: the same closure without `PassO2.SB._sizeOf_inst` and
    without every constant that references it (the `sizeOf_spec` lemmas),
    so the input is closed. No edge to the instance;
    `SA._sizeOf_1` keeps O2's relocated form (it references the lower
    component's recursor `PassO2.SB._ix.rec`, not the instance) and the
    non-canonical set is exactly `{PassO2.SA._sizeOf_1}` with a cause that
    names `PassO2.SB._sizeOf_inst`.

  Every compile must have no refusals.

  M1-h adds one input per other side condition (`runSide`, below).

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

/-! ## The other side conditions (M1-h)

Fixture `Tests/Ix/Compile/Pass/O11aSide.lean`. Every decline of O11a at the
recursion of Lean's `sizeOf` family is recorded with its cause, not only the
absent instance. One input per side condition, each the selected closure of
the upper member's `_sizeOf_1`, and the valid neighbour `N` (O11a fires, no
record). The telescope and shape conditions are hand-built from `N`'s
closure: `NB._sizeOf_inst`'s size function is replaced by `NB.sizeOfAlt` (a
recursion of `NB.rec` with another telescope) or by `NB.sizeOfWrapped` (not
`λ t. NB.rec … t`). The users' functions `NA.viaRec`/`PA.viaRec` (the same
recursors, not the `sizeOf` recursion) are in the closures and must not be
recorded: each declining input records exactly its root, with a cause naming
the condition.
-/

/-- One side-condition input. -/
structure SideCase where
  label : String
  root : Name
  inst : Name
  extra : List Name := []
  /-- The replacement for the instance's size function (hand-built cases). -/
  sizeFn? : Option Name := none
  /-- `none`: the valid neighbour (O11a fires); `some s`: the cause names `s`. -/
  cause? : Option String

def sideCases : Array SideCase := #[
  { label := "neighbour N", root := `O11aSide.NA._sizeOf_1, inst := `O11aSide.NB._sizeOf_inst,
    extra := [`O11aSide.NA.viaRec], cause? := none },
  { label := "parameters P", root := `O11aSide.PA._sizeOf_1, inst := `O11aSide.PB._sizeOf_inst,
    extra := [`O11aSide.PA.viaRec], cause? := some "has 1 parameter(s)" },
  { label := "indices I", root := `O11aSide.IA._sizeOf_1, inst := `O11aSide.IB._sizeOf_inst,
    cause? := some "index" },
  { label := "reflexive R", root := `O11aSide.RA._sizeOf_1, inst := `O11aSide.RB._sizeOf_inst,
    cause? := some "is reflexive" },
  { label := "telescope N/alt", root := `O11aSide.NA._sizeOf_1, inst := `O11aSide.NB._sizeOf_inst,
    extra := [`O11aSide.NA.viaRec], sizeFn? := some `O11aSide.NB.sizeOfAlt,
    cause? := some "recursor telescope" },
  { label := "shape N/wrapped", root := `O11aSide.NA._sizeOf_1, inst := `O11aSide.NB._sizeOf_inst,
    sizeFn? := some `O11aSide.NB.sizeOfWrapped, cause? := some "is not `λ t." }]

/-- `inst := @SizeOf.mk T k` with `k` replaced by `k'`. -/
def replaceSizeFn (cs : List (Name × ConstantInfo)) (inst k' : Name) :
    Except String (List (Name × ConstantInfo)) := do
  unless cs.any (·.1 == inst) do throw s!"{inst} not in the closure"
  unless cs.any (·.1 == k') do throw s!"{k'} not in the closure"
  cs.mapM fun (n, ci) => do
    if n != inst then return (n, ci)
    let .defnInfo v := ci | throw s!"{inst} is not a definition"
    unless v.value.getAppNumArgs == 2 do throw s!"{inst} is not `SizeOf.mk T k`"
    return (n, .defnInfo { v with value := mkApp v.value.appFn! (mkConst k') })

def runSide : IO (Array String) := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/O11aSide.lean"
  let mut errors : Array String := #[]
  for c in sideCases do
    let seeds := c.root :: c.extra ++ c.sizeFn?.toList
    let mut cs := Ix.EnvScope.collectSelectedDeps env seeds
    if let some k' := c.sizeFn? then
      match replaceSizeFn cs c.inst k' with
      | .ok cs' => cs := cs'
      | .error e =>
        errors := errors.push s!"{c.label}: {e}"
        continue
    unless cs.any (·.1 == c.inst) do errors := errors.push s!"{c.label}: the closure lacks {c.inst}"
    for mode in [true] do
      let unit : Tests.Ix.Compile.Pass3.CUnit :=
        { name := s!"o11a-{c.label}", env, seeds := seeds.toArray, closure := cs }
      let out ← Tests.Ix.Compile.Pass3.compileUnit unit
      unless out.cenv.ungrounded.isEmpty do
        errors := errors.push s!"{c.label} mode={mode}: {out.cenv.ungrounded.size} refusals"
      let nc := out.cenv.p3NonCanonical.toList
      let toInst ← IO.ofExcept (references out.env c.root c.inst)
      IO.println s!"[o11a-decline] side {c.label} mode={mode} ({cs.length} constants): \
        {c.root} references {c.inst}: {toInst}; non-canonical set \
        {nc.map fun (n, x) => s!"{n.pretty}: {x}"}"
      match c.cause? with
      | none =>
        unless nc.isEmpty do errors := errors.push s!"{c.label}: unexpected records {nc.map (·.1.pretty)}"
        unless toInst do errors := errors.push s!"{c.label}: O11a did not fire ({c.root} lacks {c.inst})"
      | some want =>
        match nc with
        | [(n, cause)] =>
          if n != ixN c.root then errors := errors.push s!"{c.label}: recorded {n.pretty}, expected {c.root}"
          unless (cause.splitOn want).length > 1 && (cause.splitOn "O11a declined").length > 1 do
            errors := errors.push s!"{c.label}: the cause does not name `{want}`: {cause}"
        | _ => errors := errors.push s!"{c.label}: expected exactly one record ({c.root}), got \
            {nc.map (·.1.pretty)}"
        if toInst then errors := errors.push s!"{c.label}: {c.root} references {c.inst} although O11a declined"
  return errors

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
    for mode in [true] do
      let unit : Tests.Ix.Compile.Pass3.CUnit :=
        { name := s!"o11a-{label}", env, seeds := #[root], closure := cs }
      let out ← Tests.Ix.Compile.Pass3.compileUnit unit
      unless out.cenv.ungrounded.isEmpty do
        errors := errors.push s!"{label} mode={mode}: {out.cenv.ungrounded.size} refusals"
      let nc := out.cenv.p3NonCanonical.toList
      IO.println s!"[o11a-decline] {label} mode={mode}: non-canonical set {nc.map fun (n, c) => s!"{n.pretty}: {c}"}"
      let toInst ← IO.ofExcept (references out.env root inst)
      let toLower ← IO.ofExcept (references out.env root lowerRec)
      IO.println s!"[o11a-decline] {label} mode={mode}: {root} references {inst}: {toInst}; {lowerRec}: {toLower}"
      if wantEdge then
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
  let sideErrors ← runSide
  errors := errors ++ sideErrors
  for e in errors do IO.println s!"[o11a-decline] FAIL {e}"
  IO.println s!"[o11a-decline] {if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}: \
    {2 + sideCases.size} inputs (Pass 3)"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.O11aDecline
