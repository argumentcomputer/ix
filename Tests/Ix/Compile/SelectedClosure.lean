import LSpec
import Ix.Meta
import Ix.EnvScope
import Tests.Ix.Compile.ClosureHarness
import IxC.Kernel.CoreDefs
import IxC.Kernel.Roles

/-!
  compiler-selected-closure: what a selected closure
  (`Ix.EnvScope.collectSelectedDeps`, `ClosureOptions.selected`) carries
  beyond the references of its declarations. No compile.

  1. **Whole logical units.** The size functions `PassO2.SA._sizeOf_1`/`_2`
     of the fixture `Tests/Ix/Compile/Fixtures/MutualSizeOf.lean` never
     mention their block's instances. A selected closure of either root,
     of both, and of both reversed carries every member's `_sizeOf_inst`,
     plus the support the unit brings (`sizeOfUnitSupport`). Each closure
     is a fixed point, and the seed order does not change it. Negative
     control: the raw closure (`collectDeps … {}`) lacks the instances.
  2. **A matcher's unit.** The on-demand auxiliary `matcher._arg_pusher` belongs to
     `matcher`'s unit, so a closure of the bare `matcher` carries it. The
     caller `carriedProof` is outside the unit and is not pulled.
  3. **Mutual siblings.** The closure of each `mutual` member of
     `Tests.Ix.Compile.AuxiliaryClosure.mutualSeeds` holds its sibling.
  4. **Checker support** (`checkerSupportOf`, derived from
     `IxC.Kernel.Roles` `Role.deps`). `Nat.land`'s support holds
     `Nat.mul` (`natOpDeps`). It is drawn from existing records only. The
     selected closure of a `Nat.land` user holds `Nat.mul`, and the raw
     closure does not. The drift check of the derivation against
     `natOpDeps` is a separate test.
  5. **Self-contained for IxC.** The selected closure of `matcher` holds
     `Nat.rec` (the certified reader declines an inductive block without
     its recursor); the raw closure does not. The selected closure of
     `greeting`, a string literal, holds the literal support
     (`literalSupportLeanNames`, `String.ofList` among them; IxC declines a
     string literal before it); the raw closure lacks `String.ofList`, and a
     closure with no string literal (`landUser`'s) does not gain it. A
     literal in a theorem's proof only (`stringInProof`, the rest of its
     closure without one) brings the support too.

  `compiler-selected-closure-e2e` (`run`, ignored) compiles the same
  fixture whole and as each selected closure:
  - the Rust compile of each closure is the Lean compile, byte for byte;
  - every Named entry of a closure's output equals the whole compile's;
  - the reversed subset is byte-identical;
  - the output decompiles to its source;
  - the certified checker accepts each root's owning record in the closure
    as `ix compile` compiles it, with binder data
    (`ClosureHarness.certifiedClosure`; the Lean entry's records carry no
    binder data, so they are not the records the default role table binds).

  Ported from a9cf3607 `Tests/Ix/Compile/SelectedClosure.lean`:
  - The "ordinary and scoped collectors agree" checks are replaced by
    fixed-point and seed-order checks: there is one collector (R01-17).
  - The `Twins.Cliques` loop is dropped with the twins corpus.
  - The donor's `introducedSupport` (LC-15b) and Pass 3 harness are gone:
    the e2e runner compiles through the ordinary compiler
    (`ClosureHarness`).
  - The e2e runner keeps the certified leg only and writes to a temporary directory, not
    `out/codex-a7/…` (R11-24).

  Run with: `lake test -- compiler-selected-closure` and
  `lake test -- --ignored compiler-selected-closure-e2e` (after
  `lake build kernel-check-ixe`).
-/

open LSpec Lean
open Tests.Ix.Compile.ClosureHarness

namespace Tests.Ix.Compile.SelectedClosure

/-! ## Declarations of check 2 and 4 (in this module, read through `get_env!`) -/

def matcher (n : Nat) : Nat := n
theorem matcher._arg_pusher : matcher 0 = 0 := rfl
theorem carriedProof : matcher 0 = 0 := matcher._arg_pusher

mutual
def evenN : Nat → Bool
  | 0 => true
  | n + 1 => oddN n
def oddN : Nat → Bool
  | 0 => false
  | n + 1 => evenN n
end

mutual
def wfEven : Nat → Bool
  | 0 => true
  | n + 1 => wfOdd n
termination_by n => n
def wfOdd : Nat → Bool
  | 0 => false
  | n + 1 => wfEven n
termination_by n => n
end

mutual
partial def pEven : Nat → Bool
  | 0 => true
  | n + 1 => pOdd n
partial def pOdd : Nat → Bool
  | 0 => false
  | n + 1 => pEven n
end

theorem oddN_one : oddN 1 = true := rfl

def mutualSeeds : List (Lean.Name × Lean.Name) := [
  (``oddN, ``evenN), (``wfOdd, ``wfEven), (``pOdd, ``pEven), (``oddN_one, ``evenN)
]

/-- A user of `Nat.land`, whose certified install needs `Nat.mul`'s record
(`natOpDeps Nat.land`), which `Nat.land`'s value does not reference. -/
def landUser (a b : Nat) : Nat := Nat.land a b

/-- A string literal, which references none of the constants IxC types it
with (`String.ofList` among them). -/
def greeting : String := "hi"

/-- A String literal in a theorem's proof only: its type and the rest of its
closure hold none, and a theorem's value is not `value?`'s by default. -/
theorem stringInProof : True := (fun (_ : String) => trivial) "hi"

/-! ## The fixture of check 1 -/

def fixture : System.FilePath := "Tests/Ix/Compile/Fixtures/MutualSizeOf.lean"

def sizeOfRoots : List Name := [`PassO2.SA._sizeOf_1, `PassO2.SA._sizeOf_2]

/-- The seed sets of check 1 and of the e2e runner: each root, both, both
reversed. -/
def seedSets : List (List Name) := sizeOfRoots.map ([·]) ++ [sizeOfRoots, sizeOfRoots.reverse]

/-- Members of the roots' unit (the unit of `PassO2.SA`'s block) that the
size functions do not reference. -/
def sizeOfInstances : List Name := [`PassO2.SA._sizeOf_inst, `PassO2.SB._sizeOf_inst]

/-- **Unverified until the first run (plan §2.5, §7).** Support the unit
brings: `SizeOf.sizeOf` is reached only through the constructors'
`sizeOf_spec` lemmas, which belong to the same unit. Lean 4.34.1 generates
them eagerly (`Lean.Meta.mkSizeOfInstances`). If a run shows it is not
carried, drop it from this list. Do not restore O11a's `compilerSupportOf`. -/
def sizeOfUnitSupport : List Name := [``SizeOf.sizeOf]

/-- The 15 `Nat` operation roles guarded by `Ix.Kernel.natOpDeps`. -/
private def natOpRoles : List Ix.Kernel.Role :=
  let opKeys : List (Ix.Kernel.Key .anon) := Ix.Kernel.natOpNames ++ Ix.Kernel.natDivModNames
  opKeys.filterMap fun
    | .role r => some r
    | _ => none

/-- Compile-time drift check: for each of the 15 `Nat` operation roles, the
operation roles derived from `Role.deps` and `Role.block` (what
`Ix.EnvScope.checkerSupportOf` draws from), plus the role itself, match
`Ix.Kernel.natOpDeps` as a set. Checked in the kernel at build time instead of
at test runtime. -/
private def checkerSupportMatchesNatOpDeps : Bool :=
  natOpRoles.length == 15 &&
  natOpRoles.all fun r =>
    let supportOps := ((r.deps.flatMap Ix.Kernel.Role.block).eraseDups.filter (· != r)).filter
      natOpRoles.contains
    let derived := (r :: supportOps).eraseDups
    let guard := ((Ix.Kernel.natOpDeps (Ix.Kernel.roleKey r : Ix.Kernel.Key .anon)).filterMap fun
      | .role q => some q
      | _ => none).eraseDups
    derived.all guard.contains && guard.all derived.contains

theorem checkerSupport_matches_natOpDeps : checkerSupportMatchesNatOpDeps = true := by decide

private def report (errors : Array String) (what : String) : AssertM Unit := do
  for e in errors do IO.println s!"[selected-closure] FAIL {e}"
  expect errors.isEmpty s!"{errors.size} {what} failure(s)"

def suite : LSpec.Spec := do
  it "selected closures carry the whole unit of PassO2.SA._sizeOf_N" do
    let env ← getFileEnv fixture
    let units := Ix.EnvScope.unitIndex env.constants
    let required := sizeOfInstances ++ sizeOfUnitSupport
    let mut errors : Array String := #[]
    for n in sizeOfRoots ++ required do
      unless env.contains n do errors := errors.push s!"fixture lacks {n}"
    let mut closures : Array (List Name) := #[]
    for seeds in seedSets do
      let closed := Ix.EnvScope.collectSelectedDepsWith env units seeds
      let ns := nameSet closed
      for n in required do
        unless ns.contains n do errors := errors.push s!"{seeds}: missing {n}"
      unless sameNames closed (Ix.EnvScope.collectSelectedDepsWith env units (closed.map (·.1))) do
        errors := errors.push s!"{seeds}: the closure is not a fixed point"
      closures := closures.push (closed.map (·.1))
    -- both roots, in either order: the same list (deterministic name order)
    unless closures[2]? == closures[3]? do
      errors := errors.push "the seed order changed the closure"
    -- negative control: the raw collector follows references only
    let raw := nameSet (Ix.EnvScope.collectDeps env sizeOfRoots {})
    for n in sizeOfInstances do
      if raw.contains n then errors := errors.push s!"raw negative control carries {n}"
    report errors "unit closure"
  it "selected closures: a matcher's unit, mutual siblings, checker support" do
    let env ← get_env!
    let units := Ix.EnvScope.unitIndex env.constants
    let mut errors : Array String := #[]
    -- 2. the matcher's unit, and nothing outside it
    let bare := nameSet (Ix.EnvScope.collectSelectedDepsWith env units [``matcher])
    let carried := nameSet (Ix.EnvScope.collectSelectedDepsWith env units [``carriedProof])
    unless carried.contains ``matcher._arg_pusher do
      errors := errors.push "carriedProof lost its explicit dependency matcher._arg_pusher"
    unless bare.contains ``matcher._arg_pusher do
      errors := errors.push "the bare matcher lost matcher._arg_pusher of its unit"
    if bare.contains ``carriedProof then
      errors := errors.push "the bare matcher pulled its caller carriedProof"
    -- 3. mutual siblings
    for (root, sibling) in mutualSeeds do
      unless (nameSet (Ix.EnvScope.collectSelectedDepsWith env units [root])).contains sibling do
        errors := errors.push s!"{root}: missing its sibling {sibling}"
    -- 4. checker support
    unless (Ix.EnvScope.checkerSupportOf env.constants ``Nat.land).contains ``Nat.mul do
      errors := errors.push "checkerSupportOf Nat.land lacks Nat.mul"
    unless (Ix.EnvScope.checkerSupportOf {} ``Nat.land).isEmpty do
      errors := errors.push "checkerSupportOf synthesized records absent from the source"
    let raw := nameSet (Ix.EnvScope.collectDeps env [``landUser] {})
    let selected := nameSet (Ix.EnvScope.collectSelectedDepsWith env units [``landUser])
    unless raw.contains ``Nat.land do
      errors := errors.push "landUser's raw closure lacks Nat.land"
    if raw.contains ``Nat.mul then
      errors := errors.push "raw negative control: landUser's raw closure carries Nat.mul"
    unless selected.contains ``Nat.mul do
      errors := errors.push "landUser's selected closure lacks Nat.mul"
    -- 5. self-contained for IxC: an inductive's recursor, and the string-literal
    -- support when a closed constant has a string literal
    unless bare.contains ``Nat.rec do
      errors := errors.push "the matcher's selected closure lacks Nat.rec"
    if (nameSet (Ix.EnvScope.collectDeps env [``matcher] {})).contains ``Nat.rec then
      errors := errors.push "raw negative control: the matcher's raw closure carries Nat.rec"
    let greeted := nameSet (Ix.EnvScope.collectSelectedDepsWith env units [``greeting])
    for n in Ix.EnvScope.literalSupportLeanNames.filter env.contains do
      unless greeted.contains n do
        errors := errors.push s!"greeting's selected closure lacks the literal support {n}"
    if (nameSet (Ix.EnvScope.collectDeps env [``greeting] {})).contains ``String.ofList then
      errors := errors.push "raw negative control: greeting's raw closure carries String.ofList"
    if selected.contains ``String.ofList then
      errors := errors.push "landUser's selected closure (no string literal) carries String.ofList"
    -- a String literal in a theorem's proof only (`value? (allowOpaque := true)`)
    let some proofCi := env.find? ``stringInProof | fail "stringInProof missing"
    let isStr : Expr → Bool | .lit (.strVal _) => true | _ => false
    unless (proofCi.type.find? isStr).isNone && Ix.EnvScope.hasStringLiteral proofCi do
      errors := errors.push "stringInProof: the literal is not in its proof only, or is not seen there"
    unless (Ix.EnvScope.collectDepsWith env units [``stringInProof] .selected).all fun (n, ci) =>
        n == ``stringInProof || !Ix.EnvScope.hasStringLiteral ci do
      errors := errors.push "stringInProof's closure holds another String literal (the case is vacuous)"
    unless (nameSet (Ix.EnvScope.collectSelectedDepsWith env units [``stringInProof])).contains ``String.ofList do
      errors := errors.push "stringInProof's selected closure (a literal in a proof) lacks String.ofList"
    report errors "selected closure"

/-- `compiler-selected-closure-e2e`: the fixture compiled whole and as each
selected closure of `seedSets`, by the Lean pipeline; the Rust compile of
each closure is byte-identical; each closure's Named entries are the whole
compile's; the reversed subset is byte-identical; the output decompiles to
its source; and the certified checker accepts each root's owning record (an
accept, not a documented decline) in the closure's certified compile with
binder data (`certifiedClosure`). Files go to a temporary directory, kept
and printed on failure. -/
def run : IO UInt32 := do
  let env ← getFileEnv fixture
  let dir ← IO.FS.createTempDir
  IO.println s!"[selected-closure-e2e] files in {dir}"
  let mut errors : Array String := #[]
  let wholeClosure := env.constants.toList
  IO.println s!"[selected-closure-e2e] whole environment: {wholeClosure.length} declarations"
  let whole ← compileClosure env wholeClosure (serialize := false)
  unless whole.cenv.ungrounded.isEmpty do
    errors := errors.push s!"whole: {whole.cenv.ungrounded.size} refusals"
  let units := Ix.EnvScope.unitIndex env.constants
  let seedClosures := seedSets.zipIdx.map fun (seeds, i) =>
    (i, seeds, Ix.EnvScope.collectSelectedDepsWith env units seeds)
  -- All 4 seed sets belong to one logical unit and must produce the exact
  -- same sorted closure name-set (seed and order invariance).
  if let some (_, _, firstClosure) := seedClosures[0]? then
    let firstNames := firstClosure.map (·.1)
    for (i, seeds, closure) in seedClosures do
      unless closure.map (·.1) == firstNames do
        errors := errors.push s!"selected-{i} {seeds}: closure name-set differs from selected-0"
  -- Deduplicate identical closure lists so we compile, decompile-check, and
  -- certify once per distinct closure list.
  let mut groups : Array (List Name × List (Name × ConstantInfo) × Array (Nat × List Name)) := #[]
  for (i, seeds, closure) in seedClosures do
    let names := closure.map (·.1)
    match groups.findIdx? (fun g => g.1 == names) with
    | some idx =>
      let (ns, c, members) := groups[idx]!
      groups := groups.set! idx (ns, c, members.push (i, seeds))
    | none =>
      groups := groups.push (names, closure, #[(i, seeds)])
  for (_, closure, members) in groups do
    let firstIdx := members[0]!.1
    let allSeeds := (members.toList.flatMap (·.2)).eraseDups
    let label := s!"selected-{firstIdx} {allSeeds}"
    let out ← compileClosure env closure
    unless out.cenv.ungrounded.isEmpty do
      errors := errors.push s!"{label}: {out.cenv.ungrounded.size} refusals"
    -- closure against whole
    for (name, named) in out.env.named do
      match whole.env.named[name]? with
      | none => errors := errors.push s!"{label}: the whole output lacks {name.pretty}"
      | some reference =>
        if let some cls := namedDiff named reference then
          errors := errors.push s!"{label}: {name.pretty}: {cls} differs from the whole compile"
    let (decompileErrors, summary) ← decompileCheck env closure out
    errors := errors ++ decompileErrors.map (s!"{label}: {·}")
    -- certification means accept, not a documented decline, of the closure as
    -- `ix compile` compiles it (binder data on; `certifiedClosure`)
    let (certEnv, certBytes) ← certifiedClosure env closure
    let certReport ← certify dir s!"selected-{firstIdx}" certBytes
    for seed in allSeeds do
      match verdictOf certReport certEnv seed with
      | .error e => errors := errors.push s!"{label}: {e}"
      | .ok v =>
        unless v.outcome == "accept" do
          errors := errors.push s!"{label}: {seed}'s owning record: {v.outcome}: {v.reason}"
    IO.println s!"[selected-closure-e2e] {label} ({members.size} seed sets): closure {closure.length}, \
      {out.bytes.size} B; {summary}"
  for e in errors do IO.println s!"[selected-closure-e2e] FAIL {e}"
  IO.println s!"[selected-closure-e2e] {errors.size} failure(s)"
  if errors.isEmpty then IO.FS.removeDirAll dir
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.SelectedClosure
