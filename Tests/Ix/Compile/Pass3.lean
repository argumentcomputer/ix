/-
  pass3: the gates of Pass 3, the faithful rewrite (`Ix.Compile.Pass`; the
  only mode of both compilers since the flip, Q2), on every fixture family:
  the aux-cert reproducers (`Tests/Ix/Compile/AuxCert/*.lean`, with the two
  in `Fixtures/`), image-gen's cases (`Tests/Ix/Compile/Image/C*.lean`), the
  twin families (`TwinsFixtures`) and the aux corpus (`validateAuxClosure`).

  Per compile unit (a fixture's closure, `Tests.Ix.Compile.Harness.Units`),
  compiled in-process by the Lean pipeline (`compileLeanInput`):

  1. **names** (`Harness.namesCheck`): every input constant is emitted or
     has a block failure; every named entry is an input constant, a reserved
     `_ix` name or a block's `Muts` entry;
  2. **decompile** (`Harness.decompileProblems`): the output, decompiled by
     the Lean decompiler, equals the source constants, but for the recorded
     roundtrip defects (`Pass3Kernels.decompileKnown`, none); the listed
     units (`Pass3Kernels.rustDecompileUnits`) through the Rust decompiler
     too (`rs_decompile_roundtrip`), with no error;
  3. **kernels** (`Harness.kernelRun`): the certified checker (`cert`),
     the Rust kernel (`rs`, meta mode) and IxC (`lean`) on every fixture constant and every
     `_ix` name of the output; every failure, and only those, in the record
     (`Pass3Kernels.table`, by cause), and each leg checks every requested
     declaration;
  4. **computation rules** (`Harness.ruleEnv`): for each changed block, the
     images of its recursors and their rule statements (proof `Eq.refl`),
     compiled into a test-only copy of the output, checked by all three legs;
  5. **display names**: every changed block has an `_ix` name;
  and every block failure is a recorded root (`Pass3Kernels.compileFailures`,
  A0's evaporation refusals), a consequence of one (REFUSED-SIBLING) or a
  recorded image refusal (`Pass3Kernels.imageRefusals`), checked both ways.

  Ported from a9cf3607's `Tests/Ix/Compile/Pass3.lean`, with the harness
  split out (R11-08, `Tests/Ix/Compile/Harness/*`) and the diagnostic modes
  in their own runner (`pass3-tools`, lane G `6dcb793e`). Not here:
  the definitional and proof-justified passes' fixtures, twin pairs and
  firing checks, O11a, cliques (batch 5); the library comparison
  (`runLib`, `pass3-lib`) and the surgery's diagnostics (`runSurgered`, the
  recheck's switch-off outputs), which needed the deleted switch and
  `Ix.Tc`; the reserved-name unit `ReservedIx`, whose drivers' check is
  `compile-reserved-mdata`'s.

  Run with: `lake test -- pass3` (tier `landing`; it needs `ix` and
  `kernel-check-ixe`, built as `IxTests`' needs). `PASS3_ONLY` restricts the
  units (comma-separated stems, `twins`, `corpus`); `PASS3_NAMES` adds a
  unit of named constants of the test environment; `PASS3_KEEP=<dir>` keeps
  the outputs; `PASS3_FAILURES=<file>` appends every kernel failure;
  `PASS3_EMIT_FAILURES=1` prints a candidate record row per unrecorded block
  failure; `PASS3_JOBS` (default 8) units at a time.
-/
import Tests.Ix.Compile.Harness.Check
import Tests.Ix.Compile.Harness.Kernels
import Tests.Ix.Compile.Pass3Kernels
import Tests.Ix.Compile.Only
import Tests.Ix.RustDecompile

open Lean

namespace Tests.Ix.Compile.Pass3

open Tests.Ix.Compile.Harness

/-! ## O11a: is Lean's mutual `_sizeOf` of a split member the instance form, by δ? -/

/-- The members of `Linear.EqCnstr`'s block (the library twins, `Oracle.Lib`). -/
def o11aMembers : List Name :=
  [`EqCnstr, `EqCnstrProof, `IneqCnstr, `IneqCnstrProof, `DiseqCnstr, `DiseqCnstrProof,
   `UnsatProof].map (`Lean.Meta.Grind.Arith.Linear ++ ·)

/-- One `rfl` per member, in a test-only copy of the twins' output:
`(fun t => @sizeOf Orig.X Orig.X._sizeOf_inst t) = (fun t => @sizeOf Twin.X
Twin.X._sizeOf_inst t)`. `Orig` is the block as Lean declares it (its
`_sizeOf_N` inline the block recursor, relocated by Pass 3 for the split);
`Twin` declares the components separately (its `_sizeOf` goes through the
instances of the other components). Both production kernel legs require the two are
definitionally equal (δ of the instances and the `_sizeOf` functions, β,
projection; no induction). -/
def o11aEnv (on : Ix.CompileM.LeanPipelineOut) : Except String (Ixon.Env × Array String) := do
  let mut env := on.env
  let mut names : Array String := #[]
  let one := _root_.Ix.Level.mkSucc _root_.Ix.Level.mkZero
  let nat := _root_.Ix.Expr.mkConst (ixN ``Nat) #[]
  let mut known : Std.HashMap _root_.Ix.Compile.ExactKey.ExactName Address := {}
  for m in o11aMembers do
    let o := `Tests.Ix.Compile.Oracle.Lib.Orig ++ m
    let t := `Tests.Ix.Compile.Oracle.Lib.Twin ++ m
    let side := fun (x : Name) =>
      _root_.Ix.Expr.mkLam (ixN `t) (_root_.Ix.Expr.mkConst (ixN x) #[])
        (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp
          (_root_.Ix.Expr.mkConst (ixN ``SizeOf.sizeOf) #[one]) (_root_.Ix.Expr.mkConst (ixN x) #[]))
          (_root_.Ix.Expr.mkConst (ixN (x ++ `_sizeOf_inst)) #[])) (_root_.Ix.Expr.mkBVar 0))
        .default
    let ty := _root_.Ix.Expr.mkForallE (ixN `t) (_root_.Ix.Expr.mkConst (ixN t) #[]) nat .default
    let lhs := side o
    let rhs := side t
    let stmt := _root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp
      (_root_.Ix.Expr.mkConst (ixN ``Eq) #[one]) ty) lhs) rhs
    let pf := _root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkApp
      (_root_.Ix.Expr.mkConst (ixN ``Eq.refl) #[one]) ty) lhs
    let name := ixN (`o11a ++ m)
    let tv : _root_.Ix.TheoremVal := {
      cnst := { name, levelParams := #[], type := stmt }, value := pf, all := #[name] }
    let (env', a) ← addConst on.cenv known env (.thmInfo tv)
    env := env'
    known := known.insert name a
    names := names.push name.pretty
  return (env, names)

/-! ## Canonical-form pins -/

/-- How a pin's term was established: byte for byte against a reference
output (`bytes`), or expression for expression with its tables differing
only in leftover entries of dropped arguments (`expressions`). -/
inductive PinKind where
  | bytes
  | expressions
  deriving BEq

/-- A constant of a unit pinned by address. -/
structure FormPin where
  unit : String
  constant : String
  kind : PinKind
  address : String

/-- The canonical call-site forms of the definitional passes' fixtures, by
address: the donor's `passSameAsSurgery` (a9cf3607), measured on 2026-10-07
at M6R slice 6, where the `bytes` rows are the legacy call-site surgery's
own addresses (its output compared at `e020a72e`) and the Rust compiler gave
the same. Their units (`Tests/Ix/Compile/Pass/{O1Perm,O2Split,O4BRecOn}.lean`)
and the passes that produce these forms came with CQ5.1 (TT-07): every pin
holds as recorded (2026-10-21, `pass3` on the CQ5.1 tree), including
`O1Perm`'s two under O6, the byte-neutrality check of O1's deletion. -/
def canonicalFormPins : List FormPin := [
  { unit := "O1Perm", constant := "PassO1.Src.Even.viaRec", kind := .bytes
    address := "731dbdffd73112be86ffd51ad4eb6993b56e022ea481b704b31548673bec5f82" },
  { unit := "O1Perm", constant := "PassO1.Src.viaRec_two", kind := .bytes
    address := "cc21e7c9769b490c0da5c447276f3aa971a1ed774938d5b88e049174a1399d8f" },
  { unit := "O2Split", constant := "PassO2.SA.viaRec", kind := .expressions
    address := "85873af53f80035607f52d83fa7b653ccfa54821664c97379495b39e3a812f40" },
  { unit := "O2Split", constant := "PassO2.SB.viaRec", kind := .expressions
    address := "f983d1c96ed723925281ee26f10aeddd6c43e69da83834c209989bd399fbee12" },
  { unit := "O4BRecOn", constant := "PassO4.Src.Odd.toNat", kind := .bytes
    address := "6083ccc0c89479a3a3a552495d925a46473543f579d241c324e4c78d73d2c2ec" },
  { unit := "O4BRecOn", constant := "PassO4.Src.Even.toNat", kind := .bytes
    address := "14c008d747384a6b658c0c1e481a978ba8dc0aeaf43f66382603291dea591706" },
  { unit := "O4BRecOn", constant := "PassO4.Src.SB.depth._f", kind := .expressions
    address := "5faf01a1f51923207be4bf3d6bcdb467bc2d75b722ae39ff68f1b065a34193f9" }]

/-- The units of `canonicalFormPins` that are not units of the suite yet
(batch 5). A pin's unit must be a unit of the suite or listed here, and a
listed unit must not be one. -/
def pendingPinUnits : List String := []

/-- The pins of one unit: each constant at its pinned address. Returns the
problems and the number of pins checked. -/
def pinProblems (u : CUnit) (out : _root_.Ix.CompileM.LeanPipelineOut) : Array String × Nat :=
  Id.run do
  let mut problems : Array String := #[]
  let mut n := 0
  for pin in canonicalFormPins do
    if pin.unit != u.name then continue
    n := n + 1
    match out.env.getAddr? (ixN (parseName pin.constant)) with
    | none => problems := problems.push s!"{u.name}: {pin.constant} missing"
    | some a =>
      if toString a != pin.address then
        problems := problems.push s!"{u.name}: {pin.constant}: address {a}, pinned {pin.address}"
  return (problems, n)


/-! ## The definitional passes' fixtures (CQ5.1, TT-07, `Tests/Ix/Compile/Pass/`)

From the donor's `pass3` suite (`jcb/ix-certify-compile` `a9cf3607`):
`O1Perm` stays an input (O1 is never ported; O6 builds its terms), the other
units exercise O2–O6. -/

/-- Pairs with one address: the pass made the permuted presentation's term
the canonical presentation's. -/
def passTwins : List (String × String × String) := [
  ("O1Perm", "PassO1.Src.Even.viaRec", "PassO1.Can.Even.viaRec"),
  ("O1Perm", "PassO1.Src.Odd.viaRecOn", "PassO1.Can.Odd.viaRecOn"),
  ("O1Perm", "PassO1.Src.viaRec_two", "PassO1.Can.viaRec_two"),
  ("O1Perm", "PassO1.Src.viaRecOn_three", "PassO1.Can.viaRecOn_three"),
  ("O3Cases", "PassO3.Src.Even.isZero", "PassO3.Can.Even.isZero"),
  ("O3Cases", "PassO3.Src.SA.isStop", "PassO3.Can.SA.isStop"),
  ("O3Cases", "PassO3.Src.SB.isLeaf", "PassO3.Can.SB.isLeaf"),
  ("O4BRecOn", "PassO4.Src.Odd.toNat", "PassO4.Can.Odd.toNat"),
  ("O4BRecOn", "PassO4.Src.Even.toNat", "PassO4.Can.Even.toNat"),
  ("O4BRecOn", "PassO4.Src.three", "PassO4.Can.three"),
  ("O4BRecOn", "PassO4.Src.SB.depth", "PassO4.Can.SB.depth"),
  ("O4BRecOn", "PassO4.Src.depth_two", "PassO4.Can.depth_two")]
  ++ o11aMembers.map fun m =>
    ("twins", s!"{`Tests.Ix.Compile.Oracle.Lib.Orig ++ m ++ `_sizeOf_inst}",
     s!"{`Tests.Ix.Compile.Oracle.Lib.Twin ++ m ++ `_sizeOf_inst}")

/-- Pass firing: the constant references (or does not reference) the named
constant. `(unit, constant, referenced name, expected)`. -/
def passRefs : List (String × String × String × Bool) := [
  -- O6 on O1's input: `recOn` goes to the Ix `recOn`; the collapsed block keeps the paired image
  ("O1Perm", "PassO1.Src.Odd.viaRecOn", "PassO1.Src.Odd._ix.recOn", true),
  ("O1Perm", "PassO1.Col.A.viaRec", "PProd", true),
  -- O3: the Ix `casesOn` of the class (permuted, split); declines on a collapsed block
  ("O3Cases", "PassO3.Src.Even.isZero", "PassO3.Src.Even._ix.casesOn", true),
  ("O3Cases", "PassO3.Src.SA.isStop", "PassO3.Src.SA._ix.casesOn", true),
  ("O3Cases", "PassO3.Src.SB.isLeaf", "PassO3.Src.SB._ix.casesOn", true),
  ("O3Cases", "PassO3.Col.A.isNil", "PassO3.Col.A._ix.casesOn", false),
  -- O4: the Ix `brecOn`/`below` (permuted pair; the split block's lower component);
  -- declines on the upper component (cross field)
  ("O4BRecOn", "PassO4.Src.Odd.toNat", "PassO4.Src.Odd._ix.brecOn", true),
  ("O4BRecOn", "PassO4.Src.Even.toNat", "PassO4.Src.Even._ix.brecOn", true),
  ("O4BRecOn", "PassO4.Src.SB.depth", "PassO4.Src.SB._ix.brecOn", true),
  ("O4BRecOn", "PassO4.Src.SA.size", "PassO4.Src.SA._ix.brecOn", false),
  -- O11a: the split upper member uses the lower member's size instance.
  ("O2Split", "PassO2.SA._sizeOf_1", "PassO2.SB._sizeOf_inst", true),
  -- O2/O6: the component recursors; the bare occurrence keeps the image constant
  ("O2Split", "PassO2.SA.viaRec", "PassO2.SA._ix.rec", true),
  ("O2Split", "PassO2.SA.viaRec", "PassO2.SB._ix.rec", true),
  ("O2Split", "PassO2.SB.viaRec", "PassO2.SB._ix.rec", true),
  ("O2Split", "PassO2.SA.recBare", "PassO2.SA.rec", true),
  -- O5: the Ix auxiliaries at universe 0
  ("O5PropSplit", "PassO5.P.toQ", "PassO5.P._ix.casesOn", true),
  ("O5PropSplit", "PassO5.Q.elim", "PassO5.Q._ix.rec", true),
  ("O5PropSplit", "PassO5.P.viaRec", "PassO5.P._ix.rec", true)]

/-- The references of a compiled constant: its own, or its block's for a
projection. -/
def constRefs (env : Ixon.Env) (addr : Address) : Option (Array Address) := do
  let c ← env.getConst? addr
  match c.info with
  | .dPrj p | .rPrj p | .iPrj p => pure (← env.getConst? p.block).refs
  | .cPrj p => pure (← env.getConst? p.block).refs
  | _ => pure c.refs

/-- The per-pass checks of one fixture unit: the twin pairs and the firing
references. Returns the problems and the number of each checked. -/
def passChecks (u : CUnit) (out : _root_.Ix.CompileM.LeanPipelineOut) :
    Array String × Nat × Nat := Id.run do
  let mut problems : Array String := #[]
  let addr := fun (s : String) => out.env.getAddr? (ixN (parseName s))
  let mut nt := 0
  for (unit, a, b) in passTwins do
    if unit != u.name then continue
    nt := nt + 1
    match addr a, addr b with
    | some x, some y =>
      if x != y then problems := problems.push s!"{u.name}: twins differ: {a} / {b}"
    | _, _ => problems := problems.push s!"{u.name}: twin missing: {a} / {b}"
  let names : Std.HashMap Address (Array String) := out.env.named.fold (init := {}) fun m n nd =>
    m.insert nd.addr ((m.getD nd.addr #[]).push n.pretty)
  let mut nr := 0
  for (unit, c, r, want) in passRefs do
    if unit != u.name then continue
    nr := nr + 1
    let some ad := addr c | problems := problems.push s!"{u.name}: {c} missing"; continue
    let some refs := constRefs out.env ad
      | problems := problems.push s!"{u.name}: {c} has no constant"; continue
    let has := refs.any fun x => (names.getD x #[]).contains r
    if has != want then
      problems := problems.push s!"{u.name}: {c} {if want then "does not reference" else "references"} {r}"
  return (problems, nt, nr)

/-! ## One unit -/

/-- The checks of one unit (see the module docstring). Returns the problems
and the report lines. -/
def runUnit (u : CUnit) (keep? : Option System.FilePath) : IO (Array String × Array String) := do
  let mut problems : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let out ← compileUnit u
  lines := lines.push s!"{u.name}: {u.seeds.size} fixture constants, {u.closure.length} in the \
closure; block failures {out.cenv.ungrounded.size} ({(← IO.monoMsNow) - t0} ms)"
  for (n, e) in out.cenv.ungrounded.toList.take 6 do
    lines := lines.push s!"  failed: {n.pretty}: {e.take 240}"
  -- 1. changed blocks and names
  let idr := namesCheck u out
  lines := lines.push s!"  changed blocks: {idr.changedBlocks.map (·.map (·.pretty))}; \
named entries: {idr.inputNames} input constants, {idr.reserved} reserved"
  problems := problems ++ idr.problems.map (s!"{u.name}: " ++ ·)
  -- 5. display names of the changed blocks' auxiliaries
  problems := problems ++ displayProblems u out idr.changedBlocks
  -- the canonical-form pins of the unit
  let (pins, nPins) := pinProblems u out
  problems := problems ++ pins
  if nPins > 0 then lines := lines.push s!"  pins: {nPins} canonical-form pin(s)"
  -- the definitional passes' twins and firing references (CQ5.1)
  let (pp, nt, nr) := passChecks u out
  problems := problems ++ pp
  if nt + nr > 0 then lines := lines.push s!"  passes: {nt} twin pairs at one address, {nr} firing checks"
  -- block failures against the record
  let emit := (← IO.getEnv "PASS3_EMIT_FAILURES").isSome
  let (fps, fls) := failureProblems u out Pass3Kernels.compileFailures Pass3Kernels.imageRefusals emit
  problems := problems ++ fps
  lines := lines ++ fls
  -- 2. decompile
  let (dps, dls) ← decompileProblems u out Pass3Kernels.decompileKnown
  problems := problems ++ dps
  lines := lines ++ dls
  if Pass3Kernels.rustDecompileUnits.contains u.name then
    let errs ← Tests.RustDecompile.rsDecompileRoundtripFFI u.closure
    lines := lines.push s!"  rust decompile: {errs.size} problem(s)"
    problems := problems ++ errs.map fun e => s!"{u.name}: rust decompile: {e.take 240}"
  -- 3. kernels on the output; 4. rules in a test-only copy
  let dir ← match keep? with
    | some d => do
      let d := d / u.name
      IO.FS.createDirAll d
      pure d
    | none => IO.FS.createTempDir
  try
    let seedSet : Std.HashSet String := u.seeds.foldl (fun s n => s.insert (ixN n).pretty) {}
    let names := out.env.named.toArray.filterMap fun (n, _) =>
      let s := n.pretty
      if seedSet.contains s || _root_.Ix.Compile.Pass.hasReserved n then some s else none
    let run ← kernelRun dir out.bytes names
    dumpRuns u.name [("suite", run)]
    -- where a row varies, the anonymous kernel on the same output decides
    -- which failures are meta-only
    let anon? : Option (Std.HashSet (String × String)) ←
      if Pass3Kernels.table.any (fun e => e.unit == u.name && e.varies) then do
        let adir := dir / "anon"
        IO.FS.createDirAll adir
        let a ← kernelRun adir out.bytes names (anon := true) (skipDeps := true)
        pure (some (a.failed.foldl (fun s (l, n, _) => s.insert (l, n)) {}))
      else pure none
    let (kps, summary) := check Pass3Kernels.table u.name run.failed run.checked run.targets.size anon?
    problems := problems ++ kps
    lines := lines.push s!"  kernels: {summary}; {run.leanSummary}"
    if !idr.changedBlocks.isEmpty && out.cenv.ungrounded.isEmpty then
      match ruleEnv out with
      | .error e => problems := problems.push s!"{u.name}: rule environment: {e}"
      | .ok (renv, images, rules) =>
        match Ixon.serEnv renv with
        | .error e => problems := problems.push s!"{u.name}: rule environment: {e}"
        | .ok bytes =>
          let rdir := dir / "rules"
          IO.FS.createDirAll rdir
          let rulesRun ← kernelRun rdir bytes (images ++ rules) (anon := true)
          let rfailed := rulesRun.failed
          lines := lines.push s!"  rules: {images.size} images, {rules.size} rule statements by \
rfl, {rfailed.size} kernel failure(s); selected {rulesRun.selected}, checked {rulesRun.checked}; {rulesRun.leanSummary}"
          for (leg, n, m) in rfailed do
            problems := problems.push s!"{u.name}: rule {leg}: {n} fails: {m.take 240}"
    if u.name == "twins" then
      match o11aEnv out with
      | .error e => problems := problems.push s!"twins: O11a equality environment: {e}"
      | .ok (env, names) =>
        match Ixon.serEnv env with
        | .error e => problems := problems.push s!"twins: O11a equality serialization: {e}"
        | .ok bytes =>
          let odir := dir / "o11a"
          IO.FS.createDirAll odir
          let failed ← kernelFailures odir bytes names (anon := true)
          lines := lines.push s!"  o11a: {names.size} rfl statements, {failed.size} kernel failure(s)"
          for (leg, n, why) in failed do
            problems := problems.push s!"twins: O11a {leg}: {n}: {why.take 240}"
  finally
    if keep?.isNone then IO.FS.removeDirAll dir
  return (problems, lines)

/-! ## The suite -/

/-- The suite's units by name. -/
def unitNames : List String := fixtureFiles.map stemOf ++ ["twins", "corpus"]

/-- The records' own checks: every row names a unit of the suite, and every
pin's unit is a unit or pending (and a pending unit is none). -/
def recordProblems : Array String := Id.run do
  let mut ps : Array String := #[]
  let known (u : String) := unitNames.contains u
  for e in Pass3Kernels.table do
    unless known e.unit do ps := ps.push s!"record: kernel row of {e.unit}, no unit of the suite"
  for r in Pass3Kernels.compileFailures do
    unless known r.unit do ps := ps.push s!"record: block failure of {r.unit}, no unit of the suite"
  for r in Pass3Kernels.imageRefusals do
    unless known r.unit do ps := ps.push s!"record: image refusal of {r.unit}, no unit of the suite"
  for r in Pass3Kernels.decompileKnown do
    unless known r.unit do ps := ps.push s!"record: decompile defect of {r.unit}, no unit of the suite"
  for u in Pass3Kernels.rustDecompileUnits do
    unless known u do ps := ps.push s!"record: Rust decompile unit {u}, no unit of the suite"
  for p in canonicalFormPins do
    unless known p.unit || pendingPinUnits.contains p.unit do
      ps := ps.push s!"record: pin {p.constant} of {p.unit}, neither a unit of the suite nor pending"
  for u in pendingPinUnits do
    if known u then ps := ps.push s!"record: {u} is a unit of the suite; remove it from pendingPinUnits"
  return ps

def run (env : Environment) : IO UInt32 := do
  -- a tool's variable selects the `pass3-tools` runner, never this suite
  for var in Pass3Kernels.toolModes do
    if (← IO.getEnv var).isSome then
      IO.println s!"[pass3] FAIL {var} is set: it selects the `pass3-tools` runner, not this suite"
      return 1
  let want ← Tests.Ix.Compile.Only.select "pass3" "PASS3_ONLY" unitNames
  let keep? := (← IO.getEnv "PASS3_KEEP").map System.FilePath.mk
  let mut units : Array (String × IO CUnit) := #[]
  for p in fixtureFiles do
    let stem := stemOf p
    if want stem then units := units.push (stem, unitOfFile p)
  if want "twins" then units := units.push ("twins", twinsUnit)
  if let some ns := ← IO.getEnv "PASS3_NAMES" then
    units := units.push ("names", pure (namesUnit env ns))
  if want "corpus" then units := units.push ("corpus", corpusUnit env)
  let mut problems : Array String := recordProblems
  for p in problems do IO.println s!"[pass3] FAIL {p}"
  let (mbe, mbeLine) := mayBeEmptyControl Pass3Kernels.table
  IO.println s!"[pass3] {mbeLine}"
  for p in mbe do IO.println s!"[pass3] FAIL {p}"
  problems := problems ++ mbe
  let pending := canonicalFormPins.filter (pendingPinUnits.contains ·.unit)
  IO.println s!"[pass3] {pending.length} canonical-form pin(s) wait for their units ({pendingPinUnits})"
  -- Units load one after the other (each elaborates its file in this process),
  -- and each loaded unit's checks start at once in a task of their own, at most
  -- `PASS3_JOBS` (default 8) at a time: the units are independent (own closure,
  -- own temporary directory, own kernel subprocesses). Every unit's lines are
  -- printed, and its problems collected, in unit order.
  let jobs := max 1 (((← IO.getEnv "PASS3_JOBS").bind String.toNat?).getD 8)
  let mut slots : Array (Option (Array String × Array String ⊕
      Task (Except IO.Error (Array String × Array String)))) := Array.replicate units.size none
  let mut live : Array (Task (Except IO.Error (Array String × Array String))) := #[]
  -- the longest units start first (their order in the log is unchanged)
  let heavy := ["twins", "corpus", "MdataSpine"]
  let order := (List.range units.size).filter (heavy.contains units[·]!.1) ++
    (List.range units.size).filter (!heavy.contains units[·]!.1)
  for i in order do
    let (stem, mk) := units[i]!
    let u? ← mk.toBaseIO
    let u ← match u? with
      | .ok u => pure u
      | .error e =>
        if leanRejects.contains stem then
          slots := slots.set! i (some <| .inl
            (#[s!"[pass3] {stem}: Lean itself rejects the file (aux-cert record)"], #[]))
        else
          slots := slots.set! i (some <| .inl (#[s!"[pass3] FAIL {stem}: {e}"], #[s!"{stem}: {e}"]))
        continue
    -- a free slot as soon as any unit finishes
    while live.size ≥ jobs do
      live ← live.filterM fun t => return !(← IO.hasFinished t)
      if live.size ≥ jobs then IO.sleep 50
    let t ← IO.asTask (prio := .dedicated) do
      try
        let (ps, lines) ← runUnit u keep?
        pure (lines.map (s!"[pass3] " ++ ·) ++ ps.map (s!"[pass3] FAIL " ++ ·), ps)
      catch e =>
        pure (#[s!"[pass3] FAIL {e}"], #[toString e])
    live := live.push t
    slots := slots.set! i (some (.inr t))
  for slot? in slots do
    let some slot := slot? | continue
    let (lines, ps) ← match slot with
      | .inl r => pure r
      | .inr t => IO.ofExcept (← IO.wait t)
    for l in lines do IO.println l
    problems := problems ++ ps
  IO.println s!"[pass3] {units.size} units, {problems.size} problem(s)"
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3
