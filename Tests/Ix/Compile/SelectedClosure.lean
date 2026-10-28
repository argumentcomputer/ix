/-
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
  2. **A matcher's unit** (design document §6.3, owner rule of
     2026-10-05). The on-demand auxiliary `matcher._arg_pusher` belongs to
     `matcher`'s unit, so a closure of the bare `matcher` carries it. The
     caller `carriedProof` is outside the unit and is not pulled.
  3. **Mutual siblings.** The closure of each `mutual` member of
     `Tests.Ix.Compile.AuxiliaryClosure.mutualSeeds` holds its sibling.
  4. **Checker support** (`checkerSupportOf`, derived from
     `IxC.Kernel.Roles` `Role.deps`; CQX.3). `Nat.land`'s support holds
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
  - the certified checker accepts each root's owning record.

  Ported from a9cf3607 `Tests/Ix/Compile/SelectedClosure.lean`:
  - The "ordinary and scoped collectors agree" checks are replaced by
    fixed-point and seed-order checks: there is one collector (R01-17).
  - The `Twins.Cliques` loop is dropped with the twins corpus.
  - The donor's `introducedSupport` (LC-15b) and Pass 3 harness are gone:
    the e2e runner compiles through the ordinary compiler
    (`ClosureHarness`).
  - The e2e runner keeps the certified leg only (no `check-rs`/
    `check-lean`) and writes to a temporary directory, not
    `out/codex-a7/…` (R11-24).

  Run with: `lake test -- compiler-selected-closure` and
  `lake test -- --ignored compiler-selected-closure-e2e` (after
  `lake build kernel-check-ixe`).
-/
import LSpec
import Ix.Meta
import Ix.EnvScope
import Tests.Ix.Compile.AuxiliaryClosure
import Tests.Ix.Compile.ClosureHarness
import IxC.Kernel.CoreDefs
import IxC.Kernel.Roles

open LSpec Lean
open Tests.Ix.Compile.ClosureHarness

namespace Tests.Ix.Compile.SelectedClosure

/-! ## Declarations of check 2 and 4 (in this module, read through `get_env!`) -/

def matcher (n : Nat) : Nat := n
theorem matcher._arg_pusher : matcher 0 = 0 := rfl
theorem carriedProof : matcher 0 = 0 := matcher._arg_pusher

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
carried, drop it from this list. Do not restore O11a's `compilerSupportOf`
(CQ5.3). -/
def sizeOfUnitSupport : List Name := [``SizeOf.sizeOf]

/-- Kernel names as Lean names. -/
private def kernelNameToLean : Ix.Kernel.Name → Name
  | .anonymous => .anonymous
  | .str p s => .str (kernelNameToLean p) s
  | .num p n => .num (kernelNameToLean p) n

/-- The checker-support derivation (`checkerSupportOf`, from `Role.deps`
with blocks) against the checker's install guard (`divModEnvGuardF` reads
`natOpDeps`): for each of the 15 `Nat` operation roles, the operation roles
in its support, plus the role itself, are exactly `natOpDeps` of its key,
as a set. A drift between `Role.deps` and `natOpDeps` would make a selected
closure miss a record the checker needs, or carry one it does not. -/
def supportDrift (env : Environment) : Array String := Id.run do
  let opKeys : List (Ix.Kernel.Key .anon) := Ix.Kernel.natOpNames ++ Ix.Kernel.natDivModNames
  let roleOf : Ix.Kernel.Key .anon → Option Ix.Kernel.Role
    | .role r => some r
    | _ => none
  let opRoles := opKeys.filterMap roleOf
  let mut errors : Array String := #[]
  unless opRoles.length == 15 do
    errors := errors.push s!"expected 15 operation roles, found {opRoles.length}"
  for r in opRoles do
    let support := Ix.EnvScope.checkerSupportOf env.constants (kernelNameToLean r.leanName)
    let supportOps := support.filterMap fun n =>
      (Ix.Kernel.Role.ofLeanName? (Ix.Kernel.Name.ofLeanName n)).filter opRoles.contains
    let derived := (r :: supportOps).eraseDups
    let guard := ((Ix.Kernel.natOpDeps (Ix.Kernel.roleKey r : Ix.Kernel.Key .anon)).filterMap
      roleOf).eraseDups
    unless derived.all guard.contains && guard.all derived.contains do
      errors := errors.push s!"{kernelNameToLean r.leanName}: support operations \
        {derived.map (kernelNameToLean ·.leanName)} ≠ natOpDeps \
        {guard.map (kernelNameToLean ·.leanName)}"
  return errors

private def report (errors : Array String) (checked : Nat) (what : String) :
    IO (Bool × Nat × Nat × Option String) := do
  for e in errors do IO.println s!"[selected-closure] FAIL {e}"
  return (errors.isEmpty, if errors.isEmpty then checked else 0, checked,
    if errors.isEmpty then none else some s!"{errors.size} {what} failure(s)")

def suite : List TestSeq := [
  .individualIO "selected closures carry the whole unit of PassO2.SA._sizeOf_N" none (do
    let env ← getFileEnv fixture
    let required := sizeOfInstances ++ sizeOfUnitSupport
    let mut errors : Array String := #[]
    for n in sizeOfRoots ++ required do
      unless env.contains n do errors := errors.push s!"fixture lacks {n}"
    let mut closures : Array (List Name) := #[]
    for seeds in seedSets do
      let closed := Ix.EnvScope.collectSelectedDeps env seeds
      let ns := nameSet closed
      for n in required do
        unless ns.contains n do errors := errors.push s!"{seeds}: missing {n}"
      unless sameNames closed (Ix.EnvScope.collectSelectedDeps env (closed.map (·.1))) do
        errors := errors.push s!"{seeds}: the closure is not a fixed point"
      closures := closures.push (closed.map (·.1))
    -- both roots, in either order: the same list (the environment's order)
    unless closures[2]? == closures[3]? do
      errors := errors.push "the seed order changed the closure"
    -- negative control: the raw collector follows references only
    let raw := nameSet (Ix.EnvScope.collectDeps env sizeOfRoots {})
    for n in sizeOfInstances do
      if raw.contains n then errors := errors.push s!"raw negative control carries {n}"
    report errors (seedSets.length + 1) "unit closure")
    (.individualIO "selected closures: a matcher's unit, mutual siblings, checker support" none (do
    let env ← get_env!
    let mut errors : Array String := #[]
    let mut checked := 0
    -- 2. the matcher's unit, and nothing outside it
    let bare := nameSet (Ix.EnvScope.collectSelectedDeps env [``matcher])
    let carried := nameSet (Ix.EnvScope.collectSelectedDeps env [``carriedProof])
    unless carried.contains ``matcher._arg_pusher do
      errors := errors.push "carriedProof lost its explicit dependency matcher._arg_pusher"
    unless bare.contains ``matcher._arg_pusher do
      errors := errors.push "the bare matcher lost matcher._arg_pusher of its unit"
    if bare.contains ``carriedProof then
      errors := errors.push "the bare matcher pulled its caller carriedProof"
    checked := checked + 1
    -- 3. mutual siblings
    for (root, sibling) in Tests.Ix.Compile.AuxiliaryClosure.mutualSeeds do
      checked := checked + 1
      unless (nameSet (Ix.EnvScope.collectSelectedDeps env [root])).contains sibling do
        errors := errors.push s!"{root}: missing its sibling {sibling}"
    -- 4. checker support
    unless (Ix.EnvScope.checkerSupportOf env.constants ``Nat.land).contains ``Nat.mul do
      errors := errors.push "checkerSupportOf Nat.land lacks Nat.mul"
    unless (Ix.EnvScope.checkerSupportOf {} ``Nat.land).isEmpty do
      errors := errors.push "checkerSupportOf synthesized records absent from the source"
    let raw := nameSet (Ix.EnvScope.collectDeps env [``landUser] {})
    let selected := nameSet (Ix.EnvScope.collectSelectedDeps env [``landUser])
    unless raw.contains ``Nat.land do
      errors := errors.push "landUser's raw closure lacks Nat.land"
    if raw.contains ``Nat.mul then
      errors := errors.push "raw negative control: landUser's raw closure carries Nat.mul"
    unless selected.contains ``Nat.mul do
      errors := errors.push "landUser's selected closure lacks Nat.mul"
    checked := checked + 1
    -- 5. self-contained for IxC: an inductive's recursor, and the string-literal
    -- support when a closed constant has a string literal
    unless (nameSet (Ix.EnvScope.collectSelectedDeps env [``matcher])).contains ``Nat.rec do
      errors := errors.push "the matcher's selected closure lacks Nat.rec"
    if (nameSet (Ix.EnvScope.collectDeps env [``matcher] {})).contains ``Nat.rec then
      errors := errors.push "raw negative control: the matcher's raw closure carries Nat.rec"
    let greeted := nameSet (Ix.EnvScope.collectSelectedDeps env [``greeting])
    for n in Ix.EnvScope.literalSupportLeanNames.filter env.contains do
      unless greeted.contains n do
        errors := errors.push s!"greeting's selected closure lacks the literal support {n}"
    if (nameSet (Ix.EnvScope.collectDeps env [``greeting] {})).contains ``String.ofList then
      errors := errors.push "raw negative control: greeting's raw closure carries String.ofList"
    if selected.contains ``String.ofList then
      errors := errors.push "landUser's selected closure (no string literal) carries String.ofList"
    -- a String literal in a theorem's proof only (`value? (allowOpaque := true)`)
    let some proofCi := env.find? ``stringInProof | throw (IO.userError "stringInProof missing")
    let isStr : Expr → Bool | .lit (.strVal _) => true | _ => false
    unless (proofCi.type.find? isStr).isNone && Ix.EnvScope.hasStringLiteral proofCi do
      errors := errors.push "stringInProof: the literal is not in its proof only, or is not seen there"
    unless (Ix.EnvScope.collectDeps env [``stringInProof] .selected).all fun (n, ci) =>
        n == ``stringInProof || !Ix.EnvScope.hasStringLiteral ci do
      errors := errors.push "stringInProof's closure holds another String literal (the case is vacuous)"
    unless (nameSet (Ix.EnvScope.collectSelectedDeps env [``stringInProof])).contains ``String.ofList do
      errors := errors.push "stringInProof's selected closure (a literal in a proof) lacks String.ofList"
    checked := checked + 1
    report errors checked "selected closure")
    (.individualIO "checker support agrees with the checker's install guard (natOpDeps)" none (do
    let env ← get_env!
    let errors := supportDrift env
    report errors 15 "checker-support drift") .done))
]

/-- `compiler-selected-closure-e2e`: the fixture compiled whole and as each
selected closure of `seedSets`, by the Lean pipeline; the Rust compile of
each closure is byte-identical; each closure's Named entries are the whole
compile's; the reversed subset is byte-identical; the output decompiles to
its source; and the certified checker accepts each root's owning record (an
accept, not a documented decline). Files go to a temporary directory, kept
and printed on failure. -/
def run : IO UInt32 := do
  let env ← getFileEnv fixture
  let dir ← IO.FS.createTempDir
  IO.println s!"[selected-closure-e2e] files in {dir}"
  let mut errors : Array String := #[]
  let wholeClosure := env.constants.toList
  IO.println s!"[selected-closure-e2e] whole environment: {wholeClosure.length} declarations"
  let whole ← compileClosure env wholeClosure
  unless whole.cenv.ungrounded.isEmpty do
    errors := errors.push s!"whole: {whole.cenv.ungrounded.size} refusals"
  let mut subsetBytes : Option ByteArray := none
  for (seeds, i) in seedSets.zipIdx do
    let label := s!"selected-{i} {seeds}"
    let closure := Ix.EnvScope.collectSelectedDeps env seeds
    let out ← compileClosure env closure
    unless out.cenv.ungrounded.isEmpty do
      errors := errors.push s!"{label}: {out.cenv.ungrounded.size} refusals"
    -- the Rust compiler on the same closure
    let rust ← rustCheck label env closure out (dir / s!"rust-{i}.ixe")
    if let some e := rust then errors := errors.push e
    -- closure against whole
    for (name, named) in out.env.named do
      match whole.env.named[name]? with
      | none => errors := errors.push s!"{label}: the whole output lacks {name.pretty}"
      | some reference =>
        if let some cls := namedDiff named reference then
          errors := errors.push s!"{label}: {name.pretty}: {cls} differs from the whole compile"
    if i == 2 then subsetBytes := some out.bytes
    if i == 3 && subsetBytes != some out.bytes then
      errors := errors.push "the reversed subset changed the bytes"
    let (decompileErrors, summary) ← decompileCheck env closure out
    errors := errors ++ decompileErrors.map (s!"{label}: {·}")
    -- certification means accept, not a documented decline
    let certReport ← certify dir s!"selected-{i}" out.bytes
    for seed in seeds do
      match verdictOf certReport out.env seed with
      | .error e => errors := errors.push s!"{label}: {e}"
      | .ok v =>
        unless v.outcome == "accept" do
          errors := errors.push s!"{label}: {seed}'s owning record: {v.outcome}: {v.reason}"
    IO.println s!"[selected-closure-e2e] {label}: closure {closure.length}, {out.bytes.size} B; \
      {summary}; Rust {if rust.isNone then "byte-identical" else "DIFFERENT"}"
  for e in errors do IO.println s!"[selected-closure-e2e] FAIL {e}"
  IO.println s!"[selected-closure-e2e] {errors.size} failure(s)"
  if errors.isEmpty then IO.FS.removeDirAll dir
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.SelectedClosure
