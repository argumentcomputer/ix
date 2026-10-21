import LSpec
import Ix.Meta
import Ix.Cert.Audit
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.SourceContract.SyntaxFixture
import Tests.Ix.Compile.ValidateAux

/-! # The certification statements on the Source-mode fixtures (`lake test -- cert-statement`)

* **Compile parity.** `Ix.Cert.compile`, the function the statements are
  about, against the IO pipeline (`Ix.CompileM.compileLeanConsts`) and the
  Rust compiler (`Ix.CompileM.rsCompileEnvFFI`), on the closure of every
  constant of `Tests.Ix.Kernel.ReaderFidelityDefs` and
  `Tests.Ix.Kernel.SourceIngressDefs`: the serialized environments
  (`Ixon.serEnv`) are byte-identical, and so are the published addresses.
  Every record and blob of `Ix.Cert.compile`'s output is at pure BLAKE3 of
  its bytes (`Ix.Cert.CompileAuthentic`), and every input constant is
  published exactly when the report does not list it as failed
  (`Ix.Cert.CompileCovers`). Both are proved now, from `compileReport`'s own
  checks (`Ix.Cert.checkReport`, CQ2.27); the checks are timed on the
  compile's result and must refuse six tampered copies of it, and the
  reference check (`Ix.Cert.referenceCycle`, Route A, B4) must find four
  planted reference cycles (two decoded, two stored as bytes), and its
  refs-only reader must agree with the decoder on every record.
  `cert-compile-parity-init` (ignored) does the same on `Init`.
* **The statements' hypotheses and conclusion, per root, on the accepted
  fixtures** (`Tests.Ix.Kernel.SourceIngress.acceptedSeeds` and the prelude's
  constants):
  - the computed closure (`Ix.Cert.closure`) is the closure the Source-mode
    test checks, and is closed under `DependsOn`;
  - Source mode accepts it under the compiler's grouping (`Ix.Cert.blocksOf`);
  - no constant of it failed in the compile's report (`Ix.Cert.NoFailure`,
    decided), and the compile publishes every constant of it
    (`Ix.Cert.Published`);
  - a dependency-first order of the compiled closure meets `ClosureOrder`
    and is accepted by the certified entry at BLAKE3 (`Ix.Cert.IxonAccepts`);
  - the reading (`Ix.Cert.reading`) reads every constant of the closure as an
    installed compiled constant with as many level parameters as it has
    level arguments, the condition under which `Commutes` can hold.
* **Binder contracts on both sides**, on declarations of the source-contract
  syntax fixture (`Tests.Ix.SourceContract.SyntaxFixture`) with input and
  result contracts on arrows, λs and lets: their source contracts resolved
  (`Ix.Compile.prepareRegisteredConstants`, as the IO pipeline does) and
  canonicalized, Source mode accepts them, and every constant's binders carry
  the same contracts in Source mode as its reading does in the certified
  entry's environment of `Ix.Cert.compile`'s output.

Importing `Ix.Cert.Audit` builds the statements' freeze with the tests. -/

namespace Tests.Ix.Cert.Statement

open LSpec
open Tests.Ix.Kernel.SourceIngress (defsModule ownModule acceptedSeeds preludeNames)

/-- The fixture modules' constants and everything they reach, as Lean
constants. -/
def fixtureConsts (leanEnv : Lean.Environment) : IO (List (Lean.Name × Lean.ConstantInfo)) := do
  let some idx := leanEnv.getModuleIdx? defsModule | throw (IO.userError "fixture module not loaded")
  let some idx' := leanEnv.getModuleIdx? ownModule | throw (IO.userError "fixture module not loaded")
  let seeds := leanEnv.constants.toList.toArray.filterMap fun (n, _) =>
    let m := leanEnv.getModuleIdxFor? n
    if m == some idx || m == some idx' then some n else none
  IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (seeds ++ #[`Nat.div] ++ preludeNames))

/-- The published addresses of two compiled environments that differ, by name. -/
def addressDiffs (a b : Ixon.Env) : Array String := Id.run do
  let mut out := #[]
  for (n, na) in a.named.toList do
    match b.named.get? n with
    | some nb => unless na.addr == nb.addr do out := out.push s!"{n}: {na.addr} vs {nb.addr}"
    | none => out := out.push s!"{n}: missing from the second"
  for (n, _) in b.named.toList do
    unless a.named.contains n do out := out.push s!"{n}: missing from the first"
  return out

/-- `Ix.CompileCovers` on one compile: the input constants published, the
failed ones, those both published and failed, and those neither. -/
def coverage (env : Ix.Environment) (ixe : Ixon.Env) (failures : Ix.Cert.Failures) :
    Nat × Nat × Array Ix.Name × Array Ix.Name :=
  env.consts.fold (init := (0, 0, #[], #[])) fun (pub, failed, both, neither) n _ =>
    match ixe.named.contains n, failures.failed n with
    | true, true => (pub, failed, both.push n, neither)
    | true, false => (pub + 1, failed, both, neither)
    | false, true => (pub, failed + 1, both, neither)
    | false, false => (pub, failed, both, neither.push n)

/-- `compileReport`'s own checks (`Ix.Cert.checkReport`, CQ2.27): timed on
the compile's result, which they must pass, and run on tampered copies of
it, each of which they must refuse. The reference check alone
(`Ix.Cert.referenceCycle`, Route A, B4) is timed on the result and must find
the cycles planted in four copies of it (two decoded, two as bytes only), and
its refs-only reader (`Ix.Cert.RecordRefs.lazyRefs`) is compared with the
decoder on every record of the result. `resolved` is the driver's
resolution map at the end of the fold (`Ix.Cert.compileUnchecked`'s third
component), which the resolution check reads; `aux` is its aux map (the fourth
component), which the original-form check reads. -/
def checkReportCases (label : String) (env : Ix.Environment) (ixe : Ixon.Env)
    (failures : Ix.Cert.Failures) (cenv : Ix.CompileM.CompileEnv) :
    IO (Array String × Array String) := do
  let resolved := cenv.nameToAddr
  let aux := cenv.auxNameToAddr
  -- `checkReport` on the driver's final environment with its resolution and
  -- aux maps replaced (the planted cases)
  let chk := fun (r a : Std.HashMap Ix.Compile.ExactKey.ExactName Address) (out : Ixon.Env × Ix.Cert.Failures) =>
    Ix.Cert.checkReport env { cenv with nameToAddr := r, auxNameToAddr := a } out
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let ok? ← IO.lazyPure fun _ => Ix.Cert.checkReport env cenv (ixe, failures)
  let t1 ← IO.monoMsNow
  match ok? with
  | .ok () => lines := lines.push s!"{label}: checkReport passes on the compile's result \
      ({t1 - t0} ms: {env.consts.size} input constants, {ixe.consts.size} records, \
      {ixe.blobs.size} blobs)"
  | .error e => errors := errors.push s!"{label}: checkReport refuses the compile's own result: {e}"
  let some n := env.consts.keys.find? (ixe.named.contains ·)
    | return (errors.push s!"{label}: no input constant is published", lines)
  let (a₁, lc₁, lc₂) ← match ixe.consts.toList with
    | (a₁, lc₁) :: (_, lc₂) :: _ => pure (a₁, lc₁, lc₂)
    | _ => return (errors.push s!"{label}: fewer than two records", lines)
  let some (b, bytes) := ixe.blobs.toList.head?
    | return (errors.push s!"{label}: no blob", lines)
  let some named := ixe.named.get? n
    | return (errors.push s!"{label}: a published input constant has no entry", lines)
  -- a different name with `n`'s stored hash (`Ix.Name`'s `==` compares hashes, so the
  -- map takes it as `n`'s key: coverage still holds, the name check does not)
  let twin : Ix.Name := .str Ix.Name.mkAnon "planted-name-hash-collision" n.getHash
  let tampered : List (String × Ixon.Env × Ix.Cert.Failures) := [
    ("a published name replaced by a different name with its name hash",
      { ixe with named := ixe.named.insert twin named }, failures),
    ("a published input constant dropped from `named`",
      { ixe with named := ixe.named.erase n }, failures),
    ("a published input constant also listed as failed", ixe,
      { failures with blocks := failures.blocks.insert n "tampered" }),
    ("a published input constant also listed as ungrounded", ixe,
      { failures with ungrounded := failures.ungrounded.insert n "tampered" }),
    ("a record's bytes replaced by another record's",
      { ixe with consts := ixe.consts.insert a₁ lc₂ }, failures),
    ("a record moved to another address",
      { ixe with consts := (ixe.consts.erase a₁).insert b lc₁ }, failures),
    ("a blob's bytes changed", { ixe with blobs := ixe.blobs.insert b (bytes.push 0) }, failures)]
  let mut refused := 0
  for (what, ixe', failures') in tampered do
    match chk resolved aux (ixe', failures') with
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a tampered report: {what}"
    | .error _ => refused := refused + 1
  lines := lines.push s!"{label}: checkReport refuses {refused} of {tampered.length} tampered reports"
  -- the name check (distinct name hashes), timed alone on the compile's result, then
  -- refusing the planted twin by its own message
  let h0 ← IO.monoMsNow
  let collision? ← IO.lazyPure fun _ => Ix.Cert.nameHashCollision env ixe
  let h1 ← IO.monoMsNow
  match collision? with
  | none => lines := lines.push s!"{label}: nameHashCollision finds no two names with one hash \
      ({env.consts.size} input and {ixe.named.size} published names, {h1 - h0} ms)"
  | some (x, y) => errors := errors.push s!"{label}: nameHashCollision finds {x.pretty} and \
      {y.pretty} in the compile's result"
  match chk resolved aux ({ ixe with named := ixe.named.insert twin named }, failures) with
  | .error e =>
    unless (e.splitOn "name check failed").length > 1 do
      errors := errors.push s!"{label}: the planted name-hash twin is refused, but not by the name check: {e}"
  | .ok () => pure ()
  -- the Muts check (a `Muts` entry's classes are its block's, as its projections
  -- publish them), timed alone on the compile's result, then refusing a planted
  -- class the block does not publish by its own message
  let m0 ← IO.monoMsNow
  let mismatch? ← IO.lazyPure fun _ => Ix.Cert.mutsMismatch ixe
  let m1 ← IO.monoMsNow
  let entries := ixe.named.toList.filter fun (_, nd) => match nd.constMeta.info with
    | .muts .. => true
    | _ => false
  match mismatch? with
  | none => lines := lines.push s!"{label}: mutsMismatch finds every Muts entry's classes at their \
      block's projections ({entries.length} entries, {m1 - m0} ms)"
  | some (e, i, h) => errors := errors.push s!"{label}: mutsMismatch finds {e.pretty}'s class {i} \
      lists {h}, not published at that member's projection, in the compile's result"
  match entries.head? with
  | none => lines := lines.push s!"{label}: no Muts entry to tamper with"
  | some (entry, nd) =>
    match nd.constMeta.info with
    | .muts all layout =>
      let planted : Ixon.Named := { nd with constMeta := { nd.constMeta with
        info := .muts (all.push #[Address.blake3Pure "planted-muts-class".toUTF8]) layout } }
      match chk resolved aux ({ ixe with named := ixe.named.insert entry planted }, failures) with
      | .error e =>
        if (e.splitOn "Muts check failed").length > 1 then
          lines := lines.push s!"{label}: checkReport refuses a Muts entry with a planted class \
            by the Muts check"
        else
          errors := errors.push s!"{label}: the planted Muts class is refused, but not by the Muts check: {e}"
      | .ok () => errors := errors.push s!"{label}: checkReport accepts a Muts entry with a planted class"
    | _ => pure ()
  -- the resolution check (every name the driver resolves is published at that
  -- address), timed alone on the compile's result, then refusing, by its own
  -- message, a resolution map moved off a published name's address, a published
  -- name's entry moved off its resolved address (as a later block's aux entry
  -- would; a name no `Muts` class lists, so the Muts check does not see it), and
  -- a resolved name that is not published
  let s0 ← IO.monoMsNow
  let unresolved? ← IO.lazyPure fun _ => Ix.Cert.resolutionMismatch resolved ixe
  let s1 ← IO.monoMsNow
  match unresolved? with
  | none => lines := lines.push s!"{label}: resolutionMismatch finds every resolved name published \
      where it resolves ({resolved.size} resolved, {ixe.named.size} published names, {s1 - s0} ms)"
  | some (n, a, b) => errors := errors.push s!"{label}: resolutionMismatch finds {n.pretty} resolved \
      to {a} but published at {b} in the compile's result"
  let listed : Std.HashSet Address := entries.foldl (init := {}) fun s (_, nd) =>
    match nd.constMeta.info with
    | .muts all _ => all.foldl (init := s) fun s cls => cls.foldl (·.insert ·) s
    | _ => s
  let elsewhere := Address.blake3Pure "planted-resolution".toUTF8
  match resolved.toList.find? fun (k, _) => ixe.named.contains k && !listed.contains (Ix.Name.getHash k) with
  | none => errors := errors.push s!"{label}: no published resolved name outside the Muts classes"
  | some (k, _) =>
    let some nd := ixe.named.get? k
      | return (errors.push s!"{label}: a published resolved name has no entry", lines)
    let unpublished : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "planted-unpublished-resolution"
    let planted : List (String × Std.HashMap Ix.Compile.ExactKey.ExactName Address × Ixon.Env) := [
      ("a resolution map moved off a published name's address",
        resolved.insert k elsewhere, ixe),
      ("a published name's entry moved off its resolved address",
        resolved, { ixe with named := ixe.named.insert k { nd with addr := elsewhere } }),
      ("a resolved name that is not published",
        resolved.insert unpublished nd.addr, ixe)]
    let mut byCheck := 0
    for (what, resolved', ixe') in planted do
      match chk resolved' aux (ixe', failures) with
      | .error e =>
        if (e.splitOn "resolution check failed").length > 1 then byCheck := byCheck + 1
        else errors := errors.push s!"{label}: {what} is refused, but not by the resolution check: {e}"
      | .ok () => errors := errors.push s!"{label}: checkReport accepts {what}"
    lines := lines.push s!"{label}: checkReport refuses {byCheck} of {planted.length} planted \
      resolutions by the resolution check"
  -- the component check (every published input inductive at an inductive
  -- projection of a block with a `Muts` entry), timed alone on the compile's
  -- result, then refusing, by its own message, the result with the `Muts` entry
  -- of a published input inductive's block dropped
  let c0 ← IO.monoMsNow
  let unseen? ← IO.lazyPure fun _ => Ix.Cert.unseenInductive env ixe
  let c1 ← IO.monoMsNow
  let inductives := env.consts.toList.filterMap fun (n, ci) => match ci with
    | .inductInfo _ => (ixe.named.get? n).map fun nd => (n, nd)
    | _ => none
  match unseen? with
  | none => lines := lines.push s!"{label}: unseenInductive finds every published input inductive at \
      an inductive projection of a block with a Muts entry ({inductives.length} published inductives, \
      {c1 - c0} ms)"
  | some n => errors := errors.push s!"{label}: unseenInductive finds {n.pretty} in the compile's result"
  let blockOf (nd : Ixon.Named) : Option Address :=
    match (Ix.Cert.storedRecord ixe nd.addr).map (·.info) with
    | some (Ixon.ConstantInfo.iPrj p) => some p.block
    | _ => none
  match inductives.findSome? fun (_, nd) => blockOf nd with
  | none => errors := errors.push s!"{label}: no published input inductive at an inductive projection"
  | some block =>
    let dropped := ixe.named.filter fun _ nd => match nd.constMeta.info with
      | .muts .. => nd.addr != block
      | _ => true
    match chk resolved aux ({ ixe with named := dropped }, failures) with
    | .error e =>
      if (e.splitOn "component check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a block's Muts entry dropped by the \
          component check ({ixe.named.size - dropped.size} entries dropped)"
      else
        errors := errors.push s!"{label}: the dropped Muts entry is refused, but not by the component check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a block's Muts entry dropped"
  -- the original-form check (every input name of the driver's final aux map
  -- published with `Named.original`), timed alone on the compile's result,
  -- then refusing, by its own message, the result with a published input name
  -- that has no original-form record planted in the aux map
  let o0 ← IO.monoMsNow
  let unoriginal? ← IO.lazyPure fun _ => Ix.Cert.unoriginalAux env aux ixe
  let o1 ← IO.monoMsNow
  let auxInputs := aux.toList.filter fun (n, _) => env.consts.contains n
  match unoriginal? with
  | none => lines := lines.push s!"{label}: unoriginalAux finds every input name of the aux map \
      published with an original-form record ({aux.size} aux names, {auxInputs.length} input, \
      {o1 - o0} ms)"
  | some n => errors := errors.push s!"{label}: unoriginalAux finds {n.pretty} in the compile's result"
  let plantable := env.consts.toList.findSome? fun (n, _) =>
    (ixe.named.get? n).bind fun nd => if nd.original.isNone then some (n, nd.addr) else none
  match plantable with
  | none => errors := errors.push s!"{label}: no published input name without an original-form record"
  | some (n, a) =>
    match chk resolved (aux.insert n a) (ixe, failures) with
    | .error e =>
      if (e.splitOn "original-form check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses an input name without an original-form \
          record planted in the aux map ({n.pretty})"
      else
        errors := errors.push s!"{label}: the planted aux name is refused, but not by the \
          original-form check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts an input name without an \
        original-form record in the aux map"
  -- the publication check (every published input name resolved or in the
  -- driver's final aux map), timed alone on the compile's result, then
  -- refusing, by its own message, the result with a published input name
  -- dropped from both maps
  let p0 ← IO.monoMsNow
  let unresolved? ← IO.lazyPure fun _ => Ix.Cert.unresolvedPublished env resolved aux ixe
  let p1 ← IO.monoMsNow
  match unresolved? with
  | none => lines := lines.push s!"{label}: unresolvedPublished finds every published input name \
      resolved or in the aux map ({ixe.named.size} published names, {p1 - p0} ms)"
  | some n => errors := errors.push s!"{label}: unresolvedPublished finds {n.pretty} in the compile's result"
  let droppable := env.consts.toList.findSome? fun (n, _) =>
    if ixe.named.contains n && resolved.contains n then some n else none
  match droppable with
  | none => errors := errors.push s!"{label}: no published, resolved input name"
  | some n =>
    match chk (resolved.erase n) (aux.erase n) (ixe, failures) with
    | .error e =>
      if (e.splitOn "publication check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a published input name dropped from \
          the resolution and aux maps ({n.pretty})"
      else
        errors := errors.push s!"{label}: the dropped published name is refused, but not by the \
          publication check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a published input name \
        neither resolved nor in the aux map"
  -- the cross-SCC check (no resolved name outside the aux map among the extra
  -- names), timed alone on the driver's final environment, then refusing, by
  -- its own message, the environment with such a name planted among the extra
  -- names
  let c0 ← IO.monoMsNow
  let cross? ← IO.lazyPure fun _ =>
    Ix.Cert.crossClaimed env cenv.nameToAddr cenv.auxNameToAddr cenv.auxGenExtraNames
  let c1 ← IO.monoMsNow
  match cross? with
  | none => lines := lines.push s!"{label}: crossClaimed finds no resolved name outside the aux map \
      among the extra names or the constructors of their inductives ({resolved.size} resolved, \
      {cenv.auxGenExtraNames.size} extra names, {c1 - c0} ms)"
  | some n => errors := errors.push s!"{label}: crossClaimed finds {n.pretty} in the compile's result"
  let primary := resolved.toList.findSome? fun (n, _) => if aux.contains n then none else some n
  match primary with
  | none => errors := errors.push s!"{label}: no resolved name outside the aux map"
  | some n =>
    let cenv' := { cenv with auxGenExtraNames := cenv.auxGenExtraNames.insert (n : Ix.Name) }
    match Ix.Cert.checkReport env cenv' (ixe, failures) with
    | .error e =>
      if (e.splitOn "cross-SCC check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a resolved name outside the aux map \
          planted among the extra names ({(n : Ix.Name).pretty})"
      else
        errors := errors.push s!"{label}: the planted extra name is refused, but not by the \
          cross-SCC check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a resolved name outside the \
        aux map among the extra names"
  -- a resolved constructor outside the aux map whose inductive is planted
  -- among the extra names: refused by the cross-SCC check; and, alone in a
  -- resolution map without its inductive, found by `crossClaimed`
  let ctorCase := resolved.toList.findSome? fun (n, a) =>
    if aux.contains n then none else
    match env.consts.get? (n : Ix.Name) with
    | some (.ctorInfo cv) =>
      match env.consts.get? cv.induct with
      | some (.inductInfo iv) => if iv.ctors.contains (n : Ix.Name) then some (n, a, cv.induct) else none
      | _ => none
    | _ => none
  match ctorCase with
  | none => errors := errors.push s!"{label}: no resolved constructor outside the aux map"
  | some (n, a, ind) =>
    let cenv' := { cenv with auxGenExtraNames := cenv.auxGenExtraNames.insert ind }
    match Ix.Cert.checkReport env cenv' (ixe, failures) with
    | .error e =>
      if (e.splitOn "cross-SCC check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a resolved constructor outside the aux map \
          whose inductive is planted among the extra names ({(n : Ix.Name).pretty} of {ind.pretty})"
      else
        errors := errors.push s!"{label}: the planted inductive is refused, but not by the cross-SCC \
          check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a resolved constructor outside \
        the aux map whose inductive is among the extra names"
    let only : Std.HashMap Ix.Compile.ExactKey.ExactName Address := ({} : Std.HashMap _ _).insert n a
    match Ix.Cert.crossClaimed env only {} (({} : Std.HashSet Ix.Name).insert ind) with
    | some m =>
      if m == (n : Ix.Name) then
        lines := lines.push s!"{label}: crossClaimed finds the constructor {m.pretty} through its \
          inductive {ind.pretty} among the extra names"
      else errors := errors.push s!"{label}: crossClaimed finds {m.pretty}, not the constructor"
    | none => errors := errors.push s!"{label}: crossClaimed misses a resolved constructor whose \
        inductive is among the extra names"
  -- the heads check (every Pass 3 head of the driver's final environment a
  -- regenerated published input name, so in the changed set), timed alone,
  -- then refusing, by its own message, the environment with a resolved name
  -- outside the changed set (so not regenerated) planted as a head
  let q0 ← IO.monoMsNow
  let foreign? ← IO.lazyPure fun _ => Ix.Cert.foreignHead env cenv.auxReport.table cenv.p3Heads ixe
  let q1 ← IO.monoMsNow
  match foreign? with
  | none => lines := lines.push s!"{label}: foreignHead finds every Pass 3 head among the regenerated names \
      ({cenv.p3Heads.size} heads, {q1 - q0} ms)"
  | some h => errors := errors.push s!"{label}: foreignHead finds {h.pretty} in the compile's result"
  let changed := Ix.Compile.ChangedSet.ofCompile { consts := env.consts } (Ix.Cert.compileBlocks env)
    cenv.auxReport.table ixe
  let outside := resolved.toList.findSome? fun (n, _) =>
    if changed.contains (n : Ix.Name) then none else some (n : Ix.Name)
  match outside with
  | none => errors := errors.push s!"{label}: no resolved name outside the changed set"
  | some n =>
    let cenv' := { cenv with p3Heads := cenv.p3Heads.insert n n }
    match Ix.Cert.checkReport env cenv' (ixe, failures) with
    | .error e =>
      if (e.splitOn "heads check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a resolved name outside the changed set \
          planted as a Pass 3 head ({n.pretty})"
      else
        errors := errors.push s!"{label}: the planted head is refused, but not by the heads check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a Pass 3 head outside the \
        changed set"
  -- the name invariant (every input constant carries the name it is stored
  -- under), timed alone, then refusing, by its own message, the input with one
  -- definition stored under another definition's name
  let m0 ← IO.monoMsNow
  let misnamed? ← IO.lazyPure fun _ => Ix.Cert.misnamedInput env
  let m1 ← IO.monoMsNow
  match misnamed? with
  | none => lines := lines.push s!"{label}: misnamedInput finds every input constant carrying its \
      name ({env.consts.size} constants, {m1 - m0} ms)"
  | some n => errors := errors.push s!"{label}: misnamedInput finds {n.pretty} in the input"
  let defs := env.consts.toList.filter fun (_, ci) => ci matches .defnInfo _
  match defs with
  | (n, _) :: (_, ci') :: _ =>
    let env' : Ix.Environment := { env with consts := env.consts.insert n ci' }
    match Ix.Cert.checkReport env' cenv (ixe, failures) with
    | .error e =>
      if (e.splitOn "name invariant failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses an input definition stored under another \
          definition's name ({n.pretty})"
      else
        errors := errors.push s!"{label}: the misnamed input is refused, but not by the name \
          invariant: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a misnamed input constant"
  | _ => errors := errors.push s!"{label}: fewer than two input definitions"
  -- the constructor check (every constructor an input inductive lists is
  -- stored as a constructor of it), timed alone, then refusing, by its own
  -- message, the input with one constructor's inductive renamed to itself
  let s0 ← IO.monoMsNow
  let stray? ← IO.lazyPure fun _ => Ix.Cert.strayConstructor env
  let s1 ← IO.monoMsNow
  match stray? with
  | none => lines := lines.push s!"{label}: strayConstructor finds every constructor of an input \
      inductive stored as its constructor ({env.consts.size} constants, {s1 - s0} ms)"
  | some c => errors := errors.push s!"{label}: strayConstructor finds {c.pretty} in the input"
  let ctorVals := env.consts.toList.filterMap fun (n, ci) => match ci with
    | .ctorInfo cv => some (n, cv)
    | _ => none
  match ctorVals with
  | (n, cv) :: _ =>
    let env' : Ix.Environment :=
      { env with consts := env.consts.insert n (.ctorInfo { cv with induct := n }) }
    match Ix.Cert.checkReport env' cenv (ixe, failures) with
    | .error e =>
      if (e.splitOn "constructor check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses an input constructor stored with another \
          inductive ({n.pretty})"
      else
        errors := errors.push s!"{label}: the stray constructor is refused, but not by the \
          constructor check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a stray input constructor"
  | [] => errors := errors.push s!"{label}: no input constructor"
  -- the failure check (every failure the driver records is an input name),
  -- timed alone, then refusing, by its own message, the driver's final
  -- environment with a failure recorded under a name no input constant has
  let f0 ← IO.monoMsNow
  let strayF? ← IO.lazyPure fun _ => Ix.Cert.strayFailure env cenv.ungrounded
  let f1 ← IO.monoMsNow
  match strayF? with
  | none => lines := lines.push s!"{label}: strayFailure finds every recorded failure an input name \
      ({cenv.ungrounded.size} failures, {f1 - f0} ms)"
  | some f => errors := errors.push s!"{label}: strayFailure finds {f.pretty} recorded as a failure"
  let planted : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "planted-stray-failure"
  let cenvF := { cenv with ungrounded := cenv.ungrounded.insert planted "planted" }
  match Ix.Cert.checkReport env cenvF (ixe, failures) with
  | .error e =>
    if (e.splitOn "failure check failed").length > 1 then
      lines := lines.push s!"{label}: checkReport refuses a failure recorded under a name no input \
        constant has ({planted.pretty})"
    else
      errors := errors.push s!"{label}: the stray failure is refused, but not by the failure check: {e}"
  | .ok () => errors := errors.push s!"{label}: checkReport accepts a failure that is not an input name"
  -- the reference check (Route A, B4), timed alone on the compile's result,
  -- then on planted cycles: records rewritten to reference themselves or each
  -- other, which `referenceCycle` must each find
  let r0 ← IO.monoMsNow
  let cycle? ← IO.lazyPure fun _ => Ix.Cert.referenceCycle ixe
  let r1 ← IO.monoMsNow
  match cycle? with
  | none => lines := lines.push s!"{label}: referenceCycle finds no cycle in the compile's result \
      ({r1 - r0} ms)"
  | some cycle => errors := errors.push s!"{label}: referenceCycle finds a cycle in the \
      compile's result: {cycle.take 5}"
  let plain := ixe.consts.toList.filterMap fun (a, lc) =>
    lc.get?.bind fun c => if Ix.Cert.refOwner a c == a then some (a, c) else none
  let some ((a₁, c₁), (a₂, c₂)) := match plain with
      | p₁ :: p₂ :: _ => some (p₁, p₂)
      | _ => none
    | return (errors.push s!"{label}: fewer than two records that are not projections", lines)
  -- each planted twice: decoded (`ofConstant`, as a cache), and as bytes only,
  -- as the compile stores records, so the refs-only reader reads them
  let refer (c : Ixon.Constant) (b : Address) : Ixon.LazyConstant :=
    Ixon.LazyConstant.ofConstant { c with refs := c.refs.push b }
  let referBytes (c : Ixon.Constant) (b : Address) : Ixon.LazyConstant :=
    let bytes := Ixon.serConstant { c with refs := c.refs.push b }
    { buf := bytes, len := bytes.size }
  let planted : List (String × Ixon.Env) := [
    ("a record that references itself", { ixe with consts := ixe.consts.insert a₁ (refer c₁ a₁) }),
    ("two records that reference each other",
      { ixe with consts := (ixe.consts.insert a₁ (refer c₁ a₂)).insert a₂ (refer c₂ a₁) }),
    ("a record that references itself, stored as bytes",
      { ixe with consts := ixe.consts.insert a₁ (referBytes c₁ a₁) }),
    ("two records that reference each other, stored as bytes",
      { ixe with consts := (ixe.consts.insert a₁ (referBytes c₁ a₂)).insert a₂ (referBytes c₂ a₁) })]
  let mut found := 0
  for (what, ixe') in planted do
    match Ix.Cert.referenceCycle ixe' with
    | none => errors := errors.push s!"{label}: referenceCycle misses a planted cycle: {what}"
    | some _ => found := found + 1
  lines := lines.push s!"{label}: referenceCycle finds {found} of {planted.length} planted cycles"
  -- the check reads each record's references without its expressions
  -- (`Ix.Cert.RecordRefs.lazyRefs`, proved equal: `Ix.Cert.RefsRead.lazyRefs_eq`);
  -- run against the full decode on every record of the result
  let d0 ← IO.monoMsNow
  let disagree ← IO.lazyPure fun _ => ixe.consts.toList.filter fun (a, lc) =>
    Ix.Cert.RecordRefs.lazyRefs a lc != lc.get?.map fun c => (c.refs, Ix.Cert.refOwner a c)
  let d1 ← IO.monoMsNow
  match disagree with
  | [] => lines := lines.push s!"{label}: the refs-only reader agrees with the decoder on all \
      {ixe.consts.size} records ({d1 - d0} ms)"
  | (a, _) :: _ => errors := errors.push s!"{label}: the refs-only reader disagrees with the \
      decoder on {disagree.length} record(s); first: {a}"
  return (errors, lines)

/-- The records a record needs (`Ix.Cert.RecordEdge`): its block, for a
projection, and the records of its reference table. -/
def edges (ixe : Ixon.Env) (a : Address) : Array Address :=
  match Ix.Cert.recordAt ixe a with
  | none => #[]
  | some c =>
    let o := Ix.Cert.ownerOf a c
    (if o != a then #[o] else #[]) ++ c.refs.filter (ixe.consts.contains ·)

/-- The compiled closure of `seeds`, dependencies first: a depth-first
postorder over `edges`. -/
def closureOrder (ixe : Ixon.Env) (seeds : Array Address) : Array Address := Id.run do
  let mut done : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  for root in seeds do
    unless ixe.consts.contains root do continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while h : stack.size > 0 do
      let (node, expanded) := stack[stack.size - 1]
      stack := stack.pop
      if expanded then
        unless done.contains node do
          done := done.insert node
          out := out.push node
      else unless done.contains node do
        stack := stack.push (node, true)
        for d in edges ixe node do
          unless done.contains d do stack := stack.push (d, false)
  return out

/-- The artifact-wide checks the quotient renaming takes (step 7.3 (iv)): every published
role name sits at its role's address (`Ix.Cert.publishedRolesBound`, which gives
`TableBound` through `Ix.Cert.tableBound_of`, and a role's published address through
`Ix.Cert.publishedAddress_role`), and every published name agrees
with the address map (`Ix.Cert.publishedAgree`, which gives `Ix.Cert.publishedAddress_id`).
Neither is vacuous: a role's published name moved to another role's address fails the
first, and a forged copy of a published name (same ingress name, another hash) at another
address fails the second. -/
def publishedCases (label : String) (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) :
    Array String × Array String := Id.run do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let roleNamed := ixe.named.toList.filterMap fun (m, d) =>
    (Ix.LeanIngress.roleOf (Ix.LeanIngress.ingressName m)).map fun r => (m, d, r)
  if Ix.Cert.publishedRolesBound t ixe then
    lines := lines.push s!"{label}: publishedRolesBound holds: {roleNamed.length} published role \
      names, each at its role's address"
  else
    errors := errors.push s!"{label}: publishedRolesBound fails"
  if Ix.Cert.publishedAgree ixe then
    lines := lines.push s!"{label}: publishedAgree holds on {ixe.named.size} published names"
  else
    errors := errors.push s!"{label}: publishedAgree fails"
  match roleNamed with
  | (m, d, r) :: _ =>
    match t.bound.toList.find? fun (s, a) => s != r && a != d.addr with
    | some (s, a) =>
      let planted := { ixe with named := ixe.named.insert m { d with addr := a } }
      if Ix.Cert.publishedRolesBound t planted then
        errors := errors.push s!"{label}: publishedRolesBound misses {m} planted at {repr s}'s address"
      else
        lines := lines.push s!"{label}: publishedRolesBound catches {m} planted at {repr s}'s address"
    | none => errors := errors.push s!"{label}: no other role's address to plant {m} at"
  | [] => lines := lines.push s!"{label}: no published role name; the planted role case is skipped"
  match ixe.named.toList.find? (fun (m, _) => m matches .str ..) with
  | some (m@(.str p s _), d) =>
    match ixe.named.toList.find? fun (_, e) => e.addr != d.addr with
    | some (_, other) =>
      let forged := Ix.Name.str p s (Address.blake3 "ix-cert forged name".toUTF8)
      let planted := { ixe with named := ixe.named.insert forged { d with addr := other.addr } }
      if Ix.Cert.publishedAgree planted then
        errors := errors.push s!"{label}: publishedAgree misses a forged copy of {m}"
      else
        lines := lines.push s!"{label}: publishedAgree catches a forged copy of {m} at another address"
    | none => lines := lines.push s!"{label}: one published address; the forged case is skipped"
  | _ => lines := lines.push s!"{label}: no published string name; the forged case is skipped"
  return (errors, lines)

/-- S1's certificate-side `Closed` for string literals (`Ix.Cert.LiteralOrder`): in the
closure order of every published record (`closureOrder`, the order a certificate is read
in), every record with a string literal comes after the stream records of the string
roles (`stringSupportOrdered`). Not vacuous: a string role's record moved right after
the first record with a string literal fails it. -/
def stringOrderCases (label : String) (t : Ix.Kernel.RoleTable) (ixe : Ixon.Env) :
    Array String × Array String := Id.run do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let seeds : Array Address := ixe.named.fold (fun acc _ d => acc.push d.addr) #[]
  let order := (closureOrder ixe seeds).toList
  let withStr := order.filter (Ix.Cert.LiteralOrder.strAt ixe)
  let owners := Ix.Cert.LiteralOrder.stringRoles.filterMap (Ix.Cert.LiteralOrder.supportOwner ixe t)
  if Ix.Cert.LiteralOrder.stringSupportOrdered ixe t order then
    lines := lines.push s!"{label}: stringSupportOrdered holds on the closure order of \
      {order.length} records: {withStr.length} with a string literal, after the \
      {owners.length} string roles' records"
  else
    errors := errors.push s!"{label}: stringSupportOrdered fails on the closure order \
      ({withStr.length} records with a string literal, {owners.length} of \
      {Ix.Cert.LiteralOrder.stringRoles.length} string roles with a stream record)"
  match withStr.head? with
  | some a =>
    match owners.find? (· != a) with
    | some b =>
      let planted := (order.filter (· != b)).flatMap fun x => if x == a then [a, b] else [x]
      if Ix.Cert.LiteralOrder.stringSupportOrdered ixe t planted then
        errors := errors.push s!"{label}: stringSupportOrdered misses {b} moved after {a}"
      else
        lines := lines.push s!"{label}: stringSupportOrdered catches a string role's record \
          moved after the first record with a string literal"
    | none => errors := errors.push s!"{label}: no string role's record to move"
  | none => lines := lines.push s!"{label}: no record with a string literal; the planted case \
      is skipped"
  return (errors, lines)

/-- The role table's bindings in a compile's result (Route A, B5a), decided by ingress
name over every published name (`publishedCases`: `Ix.Cert.publishedRolesBound`). Also
counted, not checked: the roles whose Lean name the input declares, and (B5c, on hold)
the published names that are not a role's but sit at a role-bound address. -/
def rolesCases (label : String) (env : Ix.Environment) (ixe : Ixon.Env) :
    IO (Array String × Array String) := do
  let .ok t := Ix.Kernel.Reader.defaultTable
    | return (#[s!"{label}: the default role table does not read"], #[])
  let roles := Ix.Kernel.Role.all
  let inputNames : Std.HashSet Ix.Kernel.Name :=
    env.consts.fold (fun s n _ => s.insert (Ix.LeanIngress.ingressName n)) {}
  let declared := roles.filter fun r => inputNames.contains r.leanName
  let boundAt := t.bound.foldl (init := ({} : Std.HashMap Address Ix.Kernel.Role))
    fun m (r, a) => m.insert a r
  let aliases := ixe.named.toList.filter fun (n, named) =>
    match boundAt.get? named.addr with
    | some r => Ix.LeanIngress.ingressName n != r.leanName
    | none => false
  let (errors, lines) := publishedCases label t ixe
  let (strErrors, strLines) := stringOrderCases label t ixe
  return (errors ++ strErrors, #[s!"{label}: {declared.length} of {roles.length} role names declared \
    by the input; {aliases.length} other published names at a role-bound address (B5c, counted)"] ++
    lines ++ strLines)

/-- N-READS N4 (a): no constructor of a family occurs in the family's type or in
its constructors' types (`InductiveReading.NoCtorIn`, through its check
`noCtorIn` and `noCtorIn_iff`), for every inductive of `env`. It is
`inductive_reads`' premise, proved from Source acceptance since N4 (b)
(`Ix.Cert.NoCtor.noCtor_of_checkSourceWith`); the check keeps it observed on Init+Std.
The check is not vacuous: a constructor's own constant is refused. -/
def noCtorCases (label : String) (env : Ix.Environment) : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut families := 0
  let mut constructors := 0
  let mut refused := false
  for (_, ci) in env.consts.toArray do
    let .inductInfo v := ci | continue
    let ctors : Array Ix.ConstructorVal := v.ctors.filterMap fun n =>
      match env.consts.get? n with
      | some (.ctorInfo c) => some c
      | _ => none
    if ctors.size != v.ctors.size then
      errors := errors.push s!"{v.cnst.name}: a constructor is not in the environment"
      continue
    families := families + 1
    constructors := constructors + ctors.size
    unless Ix.CompileCert.InductiveReading.noCtorIn ctors v.cnst.type &&
        ctors.all (fun c => Ix.CompileCert.InductiveReading.noCtorIn ctors c.cnst.type) do
      errors := errors.push s!"{v.cnst.name}: a constructor of the family occurs in its types"
    if let some c := ctors[0]? then
      refused := refused || !Ix.CompileCert.InductiveReading.noCtorIn ctors (Ix.Expr.mkConst c.cnst.name #[])
  unless refused do errors := errors.push "the check refuses no constructor's own constant"
  let shown := (errors.toList.take 5).map (s!"{label}: " ++ ·)
  if errors.isEmpty then
    return (#[], #[s!"{label}: NoCtorIn holds for all {families} inductives and their {constructors} \
      constructors; a constructor's own constant is refused"])
  else
    return (shown.toArray.push s!"{label}: {errors.size} failure(s)", #[])

/-! ## A constant outside the changed set (Route A, B9a) -/

/-- The clique tables' type (`Ix.Compile.ChangedSet.cliqueTables`: the clique table and
the encoding roots), computed once per compile for `unchangedFacts`. -/
abbrev CliqueTables := Std.HashMap Ix.Name (Array Ix.Name × Array Ix.Name) × Std.HashMap Ix.Name (Array Ix.Name)

/-- The references of the condensation blocks holding each member, keyed by
the member (one pass over the condensation). -/
def holdingRefs (condensed : Ix.CondensedBlocks) : Std.HashMap Ix.Name (Array (Ix.Set Ix.Name)) :=
  condensed.blocks.fold (init := {}) fun acc rep mems =>
    let refs := condensed.blockRefs.getD rep {}
    mems.fold (init := acc) fun acc m =>
      acc.alter m fun
        | some a => some (a.push refs)
        | none => some #[refs]

/-- B9a's facts (`Ix.Cert.Unchanged.Unchanged`), decided for one input name,
reading names with `Ix.Name`'s `==` (stored hashes) as the set does: in no
class of a changed component, no constructor of an inductive one's members, no
image head of its Lean block; no condensation block holding it references such
a head; not in the clique table, and no condensation block holding it
references one of Lean's encoding constants of a clique; and, published with an
original-form compile, found identical by the aux table. The clique tables
(`tables`) and the condensation blocks' references by member (`holdingOf`,
`holdingRefs`) are computed once per compile. -/
def unchangedFacts (env : Ix.Environment) (table : Ix.AuxGen.AuxTable)
    (ixe : Ixon.Env) (blocks : Array Ix.Compile.ChangedSet.Block) (heads : Std.HashSet Ix.Name)
    (tables : CliqueTables) (holdingOf : Std.HashMap Ix.Name (Array (Ix.Set Ix.Name)))
    (n : Ix.Name) : Bool :=
  let inductives := blocks.filter (·.kind == .inductiveBlock)
  let member := blocks.all fun b => b.classes.all fun cls => !cls.contains n
  let ctor := inductives.all fun b => b.classes.all fun cls => cls.all fun m =>
    match env.get? m with
    | some (.inductInfo v) => !v.ctors.contains n
    | _ => true
  let head := !heads.contains n
  -- the references of the condensation blocks that hold `n`
  let holding : Array (Ix.Set Ix.Name) := holdingOf.getD n #[]
  let caller := holding.all fun refs => refs.toList.all fun r => !heads.contains r
  let clique := !tables.1.contains n
  let cliqueCaller := holding.all fun refs => refs.toList.all fun r =>
    (Ix.Compile.Pass.Clique.encodingOwner? tables.2 r).isNone
  let original := match ixe.named.get? n with
    | some named => !named.original.isSome || !(env.get? n).isSome || table.identical n
    | none => true
  member && ctor && head && caller && clique && cliqueCaller && original

/-- B9a on one compile, with its condensation and aux table: the facts of
every input name against the set (over the input's map, as the statements
read it): a name outside the set has them all (what `avoids_unchanged`
proves), and a name in the set fails one (the facts single the set out). -/
def unchangedCases (label : String) (env : Ix.Environment) (condensed : Ix.CondensedBlocks)
    (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env) : Array String × Array String := Id.run do
  let env : Ix.Environment := { consts := env.consts }
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let cs := Ix.Compile.ChangedSet.ofCompile env condensed table ixe
  -- computed once: the clique tables and the blocks holding each name
  let tables := Ix.Compile.ChangedSet.cliqueTables env condensed
  let holdingOf := holdingRefs condensed
  let blocks := Ix.Compile.ChangedSet.changedBlocks env ixe
  let heads : Std.HashSet Ix.Name := blocks.foldl (init := {}) fun s b =>
    if b.kind == .inductiveBlock then
      (Ix.Compile.Pass.imageKinds env.get? b.all).foldl (·.insert ·) s
    else s
  let mut inSet := 0
  let mut unchanged := 0
  let mut wrong : Array String := #[]
  for (n, _) in env.consts do
    let member := cs.contains n
    let facts := unchangedFacts env table ixe blocks heads tables holdingOf n
    if member then inSet := inSet + 1
    if facts then unchanged := unchanged + 1
    if member == facts then wrong := wrong.push s!"{n.pretty} ({if member then "in the set, has the facts" else "outside the set, lacks a fact"})"
  if wrong.isEmpty then
    lines := lines.push s!"{label}: B9a: {env.consts.size} input names, {inSet} in the changed set \
      ({blocks.size} changed components), {unchanged} with the facts, exactly the others"
  else
    errors := errors.push s!"{label}: B9a: {wrong.size} names where the set and the facts disagree: \
      {wrong.toList.take 5}"
  return (errors, lines)

/-- `Ix.Cert.compile` against the IO pipeline and the Rust compiler on
`consts`: errors, and lines for the report. `compile` is `compileReport`'s
first component (`Ix.Cert.compile_eq_ok`), and `compileReport` is
`compileUnchecked` followed by `checkReport` against the resolution map
`compileUnchecked` returns, which `checkReportCases` runs (and times) here
and requires to pass; the report's failures are checked against the artifact
(`Ix.Cert.CompileCovers`). -/
def parity (label : String) (consts : List (Lean.Name × Lean.ConstantInfo)) (workers : Nat) :
    IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let t0 ← IO.monoMsNow
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts.toArray workers
  let t1 ← IO.monoMsNow
  let pure? ← IO.lazyPure fun _ => Ix.Cert.compileUnchecked env
  let t2 ← IO.monoMsNow
  let (ixe, failures, cenv) ← match pure? with
    | .ok out => pure out
    | .error e => return (#[s!"{label}: Ix.Cert.compile failed: {e}"], lines)
  -- `CompileCovers`: every input constant published exactly when it did not fail
  let (published, failed, both, neither) := coverage env ixe failures
  if both.isEmpty && neither.isEmpty then
    lines := lines.push s!"{label}: CompileCovers: of {env.consts.size} input constants \
      {published} published, {failed} failed, none both, none neither"
  else
    errors := errors.push s!"{label}: CompileCovers: {both.size} input constants both \
      published and failed ({both.toList.take 5}), {neither.size} neither \
      ({neither.toList.take 5}); {published} published, {failed} failed"
  let some pureBytes := (Ixon.serEnv ixe).toOption
    | return (#[s!"{label}: serEnv of Ix.Cert.compile's output failed"], lines)
  lines := lines.push s!"{label}: {consts.length} constants; canon {t1 - t0} ms, \
    Ix.Cert.compile {t2 - t1} ms: {ixe.consts.size} records, {ixe.named.size} names, \
    {pureBytes.size} bytes"
  -- `CompileAuthentic`: every record and blob at pure BLAKE3 of its bytes
  let t5 ← IO.monoMsNow
  let badRecords := ixe.consts.fold (init := (#[] : Array Address)) fun out a lc =>
    if a == Address.blake3Pure lc.rawBytes then out else out.push a
  let badBlobs := ixe.blobs.fold (init := (#[] : Array Address)) fun out a bytes =>
    if a == Address.blake3Pure bytes then out else out.push a
  let t6 ← IO.monoMsNow
  if badRecords.isEmpty && badBlobs.isEmpty then
    lines := lines.push s!"{label}: CompileAuthentic: all {ixe.consts.size} records and \
      {ixe.blobs.size} blobs are at pure BLAKE3 of their bytes ({t6 - t5} ms)"
  else
    errors := errors.push s!"{label}: CompileAuthentic: {badRecords.size} records and \
      {badBlobs.size} blobs are not at pure BLAKE3 of their bytes: \
      {(badRecords ++ badBlobs).toList.take 5}"
  -- `compileReport`'s own checks (CQ2.27)
  let (checkErrors, checkLines) ← checkReportCases label env ixe failures cenv
  errors := errors ++ checkErrors
  lines := lines ++ checkLines
  -- the role table's bindings (Route A, B5a)
  let (roleErrors, roleLines) ← rolesCases label env ixe
  errors := errors ++ roleErrors
  lines := lines ++ roleLines
  -- a constant outside the changed set (Route A, B9a)
  let (unchangedErrors, unchangedLines) :=
    unchangedCases label env (Ix.Cert.compileBlocks env) cenv.auxReport.table ixe
  errors := errors ++ unchangedErrors
  lines := lines ++ unchangedLines
  -- the IO pipeline
  let t3 ← IO.monoMsNow
  match ← Ix.CompileM.compileLeanConsts consts (numWorkers := workers) with
  | .error e => errors := errors.push s!"{label}: compileLeanConsts failed: {e}"
  | .ok out =>
    let t4 ← IO.monoMsNow
    lines := lines.push s!"{label}: compileLeanConsts {t4 - t3} ms: {out.bytes.size} bytes, \
      {out.ungroundedCount} ungrounded, {out.cenv.ungrounded.size} per-block failures"
    unless out.bytes == pureBytes do
      errors := errors.push s!"{label}: serEnv bytes differ from compileLeanConsts's \
        ({pureBytes.size} vs {out.bytes.size})"
    let diffs := addressDiffs ixe out.env
    unless diffs.isEmpty do
      errors := errors.push s!"{label}: {diffs.size} published addresses differ from \
        compileLeanConsts's: {diffs.toList.take 5}"
  -- the Rust compiler
  let raw ← Ix.CompileM.rsCompileEnvFFI consts
  let rust := raw.toEnv
  match Ixon.serEnv rust with
  | .error e => errors := errors.push s!"{label}: serEnv of the Rust output failed: {e}"
  | .ok rustBytes =>
    lines := lines.push s!"{label}: Rust compiler: {rust.consts.size} records, {rustBytes.size} bytes"
    unless rustBytes == pureBytes do
      errors := errors.push s!"{label}: serEnv bytes differ from the Rust compiler's \
        ({pureBytes.size} vs {rustBytes.size})"
    let diffs := addressDiffs ixe rust
    unless diffs.isEmpty do
      errors := errors.push s!"{label}: {diffs.size} published addresses differ from the \
        Rust compiler's: {diffs.toList.take 5}"
  return (errors, lines)

/-! ## The Ixon side of one closure -/

/-- The compiled closure of `seeds` as a set, by a separate worklist. -/
def reach (ixe : Ixon.Env) (seeds : Array Address) : Std.HashSet Address := Id.run do
  let mut seen : Std.HashSet Address := {}
  let mut todo := seeds.filter (ixe.consts.contains ·)
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains a then continue
    seen := seen.insert a
    todo := todo ++ edges ixe a
  return seen

/-- `ClosureOrder`'s three conditions, decided on one order: the failures. -/
def closureOrderProblems (ixe : Ixon.Env) (seeds : Array Address) (order : Array Address) :
    Array String := Id.run do
  let mut out := #[]
  let mut position : Std.HashMap Address Nat := {}
  for (a, i) in order.zipIdx do
    if position.contains a then out := out.push s!"{a} occurs twice"
    position := position.insert a i
  let reached := reach ixe seeds
  unless reached.size == position.size && order.all reached.contains do
    out := out.push s!"the order has {position.size} records, the closure {reached.size}"
  for (a, i) in order.zipIdx do
    let some c := Ix.Cert.recordAt ixe a | out := out.push s!"{a} does not decode"
    for r in c.refs do
      if let some cr := Ix.Cert.recordAt ixe r then
        let b := Ix.Cert.ownerOf r cr
        if b != a then
          unless (position[b]?.map (decide <| · < i)).getD false do
            out := out.push s!"{a} comes before {b}, which it references"
  return out

/-- Bounds wide enough for a whole compiled library
(`Benchmarks.Kernel.CheckIxeEntry.limits`). -/
def limits : Ix.Kernel.Admission.Limits := ⟨1 <<< 22, 1 <<< 22, 1 <<< 34, 1 <<< 28, 1 <<< 26⟩

/-- The statements' hypotheses and conclusion on the closure of the accepted
fixtures: errors, and lines for the report. -/
def perRoot (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let env := Tests.Ix.Kernel.SourceIngressStep.canon (← fixtureConsts leanEnv).toArray
  let roots := (acceptedSeeds ++ preludeNames).toList.map Ix.Name.fromLeanName
  for r in roots do
    unless env.consts.contains r do errors := errors.push s!"root {r} is not in the environment"
  -- the closure, against the Source-mode test's
  let sub := Ix.Cert.closure env roots
  let expected ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv acceptedSeeds
  let extra := sub.consts.toList.filter fun (n, _) => !expected.consts.contains n
  let missing := expected.consts.toList.filter fun (n, _) => !sub.consts.contains n
  unless extra.isEmpty && missing.isEmpty do
    errors := errors.push s!"closure: {extra.length} constants the Source-mode test's closure \
      lacks ({(extra.map (·.1)).take 5}), {missing.length} it has ({(missing.map (·.1)).take 5})"
  -- closed under `DependsOn`, as `ClosureCorrect` states
  let recursors := Ix.Cert.recursorsByBlock env
  let mut open_ : Array String := #[]
  for (n, ci) in sub.consts.toList do
    for d in Ix.Cert.dependencies recursors ci do
      if env.consts.contains d && !sub.consts.contains d then open_ := open_.push s!"{n} → {d}"
  unless open_.isEmpty do
    errors := errors.push s!"closure: not closed: {open_.toList.take 5}"
  lines := lines.push s!"closure of {roots.length} roots in {env.consts.size} constants: \
    {sub.consts.size} constants, closed under DependsOn"
  -- Source acceptance
  let some envS := (Ix.LeanIngress.checkSourceBundled sub (Ix.Cert.blocksOf sub)).toOption
    | return (errors.push "Source mode refuses the closure under Ix.Cert.blocksOf", lines)
  lines := lines.push s!"Source accepts the closure: {envS.consts.length} kernel constants"
  -- no constant of the closure failed (`NoFailure`, decided on the report),
  -- and the compile publishes the closure (`Published`, which `CompileCorrect`
  -- concludes from it)
  let some (ixe, failures) := (Ix.Cert.compileReport env).toOption
    | return (errors.push "Ix.Cert.compileReport failed", lines)
  if decide (Ix.Cert.NoFailure failures sub) then
    lines := lines.push s!"no constant of the closure failed (NoFailure, decided)"
  else
    errors := errors.push "a constant of the closure failed (NoFailure is false)"
  -- the role bindings over every published name (B5a, by ingress name,
  -- `Ix.Cert.publishedRolesBound`): a role-name collision planted outside the closure is caught
  match Ix.Kernel.Reader.defaultTable with
  | .error e => errors := errors.push s!"the default role table does not read: {e}"
  | .ok t =>
    unless Ix.Cert.publishedRolesBound t ixe do
      errors := errors.push "publishedRolesBound fails on the artifact"
    let subNames : Std.HashSet Ix.Kernel.Name :=
      sub.consts.fold (fun s n _ => s.insert (Ix.LeanIngress.ingressName n)) {}
    let outside := ixe.named.toList.filterMap fun (m, d) =>
      let n := Ix.LeanIngress.ingressName m
      if subNames.contains n then none
      else (Ix.Kernel.Role.all.find? (·.leanName == n)).map fun r => (m, d, r)
    match outside with
    | (m, d, r) :: _ =>
      match Ix.Kernel.Role.all.find? (fun s => s != r && (t.addressOf? s).isSome &&
          t.addressOf? s != some d.addr) with
      | some s =>
        let some other := t.addressOf? s | errors := errors.push s!"{repr s} is not bound"
        let planted := { ixe with named := ixe.named.insert m { d with addr := other } }
        if Ix.Cert.publishedRolesBound t planted then
          errors := errors.push s!"roles: the planted collision at {m} is not caught"
        else
          lines := lines.push s!"roles: {m} (outside the closure) planted at {repr s}'s address: \
            publishedRolesBound catches it"
      | none => errors := errors.push "roles: no other bound role to plant a collision at"
    | [] => errors := errors.push "roles: no role name outside the closure to plant a collision at"
  let unpublished := sub.consts.toList.filter fun (n, _) => !ixe.named.contains n
  unless unpublished.isEmpty do
    errors := errors.push s!"{unpublished.length} constants of the closure are not published: \
      {(unpublished.map (·.1)).take 5}"
  let seeds : Array Address := sub.consts.toArray.filterMap fun (n, _) =>
    (ixe.named.get? n).map (·.addr)
  let mut byAddress : Std.HashMap Address Nat := {}
  for a in seeds do byAddress := byAddress.insert a (byAddress.getD a 0 + 1)
  let aliased := byAddress.fold (fun k _ c => if c > 1 then k + c else k) 0
  -- the compiled closure in a dependency-first order
  let order := closureOrder ixe seeds
  for p in (closureOrderProblems ixe seeds order).toList.take 5 do
    errors := errors.push s!"ClosureOrder: {p}"
  -- S1's certificate-side `Closed` for string literals, on the order the closure is read in
  match Ix.Kernel.Reader.defaultTable with
  | .error e => errors := errors.push s!"the default role table does not read: {e}"
  | .ok t =>
    let withStr := order.toList.filter (Ix.Cert.LiteralOrder.strAt ixe)
    if Ix.Cert.LiteralOrder.stringSupportOrdered ixe t order.toList then
      lines := lines.push s!"stringSupportOrdered holds on the closure's order \
        ({withStr.length} records with a string literal)"
    else
      errors := errors.push s!"stringSupportOrdered fails on the closure's order \
        ({withStr.length} records with a string literal)"
  let records := Ix.Cert.recordsOf ixe order.toList
  let blobs := Ix.Cert.blobsOf ixe order.toList
  lines := lines.push s!"compiled closure: {seeds.size} published addresses \
    ({byAddress.size} distinct; {aliased} names share an address), {order.size} records, \
    {blobs.length} blobs"
  let some binding := Ix.Kernel.Admission.defaultBinding.toOption
    | return (errors.push "the default role table does not load", lines)
  let envA ← match Ixon.Authenticated.checkBytes binding limits records blobs (Ix.Cert.hintsOf ixe) with
    | .ok envA => pure envA
    | .error e => return (errors.push s!"the certified entry refuses the compiled closure: {e}", lines)
  lines := lines.push s!"the certified entry accepts it: {envA.consts.length} kernel constants"
  -- the reading
  let some cx := Ix.Cert.admissionContext binding limits ixe order.toList
    | return (errors.push "no admission context", lines)
  let mut read := 0
  let mut unread : Array (Ix.Kernel.Key .source) := #[]
  let mut bad : Array String := #[]
  for c in envS.consts do
    match Ix.Cert.reading ixe cx c with
    | none => unread := unread.push c.name
    | some t@(.const k us) =>
      read := read + 1
      match envA.find? k with
      | none => bad := bad.push s!"{c.name} reads as {k}, which is not installed"
      | some ci =>
        unless us.length == ci.toConstantVal.levelParams.length do
          bad := bad.push s!"{c.name} reads as {repr t}: {ci.toConstantVal.levelParams.length} \
            level parameters"
    | some t => bad := bad.push s!"{c.name} reads as {repr t}"
  for b in bad.toList.take 5 do errors := errors.push s!"reading: {b}"
  -- every constant of the closure is read
  let subNames : Std.HashSet (Ix.Kernel.Key .source) :=
    sub.consts.fold (fun s n _ => s.insert (Ix.LeanIngress.ingressKey n)) {}
  let unreadOwn := unread.filter subNames.contains
  unless unreadOwn.isEmpty do
    errors := errors.push s!"reading: {unreadOwn.size} constants of the closure are not read: \
      {unreadOwn.toList.take 5}"
  lines := lines.push s!"reading: {read} of {envS.consts.length} Source constants read, \
    all installed with their level arity; not read: {unread.size}, none from the closure \
    (for example {unread.toList.take 6})"
  return (errors, lines)

/-! ## Binder contracts on both sides -/

def syntaxModule : Lean.Name := `Tests.Ix.SourceContract.SyntaxFixture

/-- Declarations of the syntax fixture whose binders carry contracts: inputs,
arrow results, λs, and value and borrow lets. -/
def contractSeeds : Array Lean.Name := #[`linear, `unique, `erased, `dependent, `withInstance,
  `localResult, `localUniqueResult, `curriedResult, `dependentArrow, `anonymousArrow,
  `quantified, `nestedLambda, `lambdaDefinition, `localLet, `sharedLoan].map (syntaxModule ++ ·)

abbrev Contracts := List (Ixon.BinderContract × Ixon.ValueContract)

/-- The contracts of a term's binders, in preorder. -/
def contractsOf : Ix.Kernel.Expr md → Contracts
  | .lam t b m | .forallE t b m => (m.contract, m.result) :: (contractsOf t ++ contractsOf b)
  | .app f a => contractsOf f ++ contractsOf a
  | .letE t v b _ => contractsOf t ++ contractsOf v ++ contractsOf b
  | .proj _ _ e | .fvar _ e => contractsOf e
  | _ => []

/-- An installed constant's type's and value's binder contracts. -/
def installedContracts : Ix.Kernel.ConstantInfo md → Contracts × Contracts
  | .defnInfo cv v _ => (contractsOf cv.type, contractsOf v)
  | .thmInfo cv v => (contractsOf cv.type, contractsOf v)
  | ci => (contractsOf ci.toConstantVal.type, [])

/-- The resolved syntax fixtures in Source mode and through `Ix.Cert.compile`
and the certified entry: errors, and lines for the report. -/
def contractAgreement (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv (contractSeeds ++ preludeNames))
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let envS ← match Ix.LeanIngress.checkSource env (Ix.Cert.blocksOf env) with
    | .ok envS => pure envS
    | .error e => return (#[s!"Source mode refuses the resolved fixtures: {e}"], lines)
  let ixe ← match Ix.Cert.compile env with
    | .ok ixe => pure ixe
    | .error e => return (#[s!"Ix.Cert.compile failed on the resolved fixtures: {e}"], lines)
  let seeds : Array Address := env.consts.toArray.filterMap fun (n, _) => (ixe.named.get? n).map (·.addr)
  let order := closureOrder ixe seeds
  let records := Ix.Cert.recordsOf ixe order.toList
  let blobs := Ix.Cert.blobsOf ixe order.toList
  let some binding := Ix.Kernel.Admission.defaultBinding.toOption
    | return (#["the default role table does not load"], lines)
  let envA ← match Ixon.Authenticated.checkBytes binding limits records blobs (Ix.Cert.hintsOf ixe) with
    | .ok envA => pure envA
    | .error e => return (#[s!"the certified entry refuses the compiled fixtures: {e}"], lines)
  let some cx := Ix.Cert.admissionContext binding limits ixe order.toList
    | return (#["no admission context"], lines)
  let mut contracted : Array Lean.Name := #[]
  let mut seen : Std.HashMap Lean.Name (Contracts × Contracts) := {}
  for n in contractSeeds do
    let some c := envS.find? (Ix.Kernel.Key.ofName (Ix.Kernel.Name.ofLeanName n))
      | errors := errors.push s!"{n}: not installed in Source mode"
    let some (.const k _) := Ix.Cert.reading ixe cx c
      | errors := errors.push s!"{n}: not read"
    let some ci := envA.find? k
      | errors := errors.push s!"{n}: its reading {k} is not installed"
    let s := installedContracts c
    let a := installedContracts ci
    unless s == a do errors := errors.push s!"{n}: Source {repr s} but Ixon {repr a}"
    if (s.1 ++ s.2).any (· != (.many, .shared)) then contracted := contracted.push n
    seen := seen.insert n s
  -- every declaration keeps a binder contract on both sides except `localLet`,
  -- whose only contract is its `let`'s: erased on both sides, as the checker's
  -- `letE` has no field for it
  let letOnly := syntaxModule ++ `localLet
  unless contracted == contractSeeds.filter (· != letOnly) do
    errors := errors.push s!"declarations that keep a contract: {contracted}"
  -- the resolved contracts themselves
  let expect (n : Lean.Name) (s : Contracts × Contracts) :=
    seen.get? (syntaxModule ++ n) == some s
  unless expect `linear ([(.linear, .shared)], [(.linear, .shared)]) &&
      expect `localUniqueResult
        ([({ uses := .linear, value := .localUnique }, .localUnique)],
          [({ uses := .linear, value := .localUnique }, .shared)]) &&
      expect `anonymousArrow ([(.many, .localUnique)], [(.many, .shared)]) do
    errors := errors.push s!"unexpected contracts: {repr (seen.toList.filter fun (n, _) =>
      [`linear, `localUniqueResult, `anonymousArrow].any (syntaxModule ++ · == n))}"
  lines := lines.push s!"contracts: {env.consts.size} resolved constants; Source accepts them \
    ({envS.consts.length} kernel constants), the certified entry accepts the compile \
    ({envA.consts.length}); {contractSeeds.size} declarations with contracts, each carrying the \
    same contracts on both sides ({contracted.size} keep one; `localLet`'s is a `let`'s)"
  return (errors, lines)

/-- Route A, B6b: `Ix.Cert.RoleClosure.RoleEvidenceChecks` on the committed RoleData, through
its executed check (`roleEvidenceCheck`, `roleEvidenceChecks_of_check`): the pinned closure
defines every well-founded `Nat` operation and the verified fold accepts it under the default
table's evidence. Run after every regeneration (RoleData's header recipe). -/
def roleEvidenceCase : IO (Array String × Array String) := do
  match Ix.Cert.RoleClosure.preparedDefault with
  | .error e => return (#[s!"the committed role closure does not prepare: {e}"], #[])
  | .ok (ev, ds) =>
    if Ix.Cert.RoleClosure.roleEvidenceCheck then
      return (#[], #[s!"role evidence: the pinned closure ({ds.length} declarations, \
        {ev.length} evidence entries) defines every well-founded operation and the verified fold \
        accepts it: RoleEvidenceChecks holds"])
    else
      let defines := Ix.Cert.RoleClosure.definesAll ds
      let run := match Ix.Kernel.Cached.checkDecls .verified ev ds.toArray with
        | .ok _ => "accepts" | .error (e, i) => s!"refuses at {i}: {e}"
      return (#[s!"role evidence: defines every operation: {defines}; the fold {run}"], #[])

/-- Source at the pinned bundle evidence (owner, 2026-10-20): the statement closure of
`Nat.div`, a well-founded `Nat` operation whose evidence the closure does not carry, is
accepted by `checkSourceBundled` (`SourceAccepts`' check); `checkSource`, at the input's own
evidence, declines it. -/
def natDivClosure (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[`Nat.div])
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let sub := Ix.Cert.closure env [Ix.Name.fromLeanName `Nat.div]
  match Ix.LeanIngress.checkSourceBundled sub (Ix.Cert.blocksOf sub) with
  | .error e => return (#[s!"Nat.div's closure ({sub.consts.size} constants) is declined at the \
      bundle evidence: {e}"], #[])
  | .ok envS =>
    let own := match Ix.LeanIngress.checkSource sub (Ix.Cert.blocksOf sub) with
      | .ok _ => "accepts it too"
      | .error _ => "declines it"
    return (#[], #[s!"Nat.div's statement closure: {sub.consts.size} constants; Source at the bundle \
      evidence accepts it ({envS.consts.length} kernel constants); at the input's own evidence, Source \
      {own}"])

/-- Literal support in `DependsOn` (owner, 2026-10-20): the statement closure of a root
with a `String` literal (`outOfBounds`, a `panic!` message) holds the constants IxC checks
the literal against (`Ix.Cert.literalSupport`), and Source at the bundle evidence accepts it. -/
def literalClosure (leanEnv : Lean.Environment) (root : Lean.Name) : IO (Array String × Array String) := do
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[root])
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let sub := Ix.Cert.closure env [Ix.Name.fromLeanName root]
  let literal := sub.consts.toList.filter fun (_, ci) => (Ix.Cert.termsOf ci).any Ix.Cert.hasStrLit
  if literal.isEmpty then return (#[s!"{root}: no string literal in its closure"], #[])
  let support := Ix.Cert.supportNames Ix.Kernel.Reader.strLitSupportNames
  let missing := support.filter fun n => !sub.consts.contains n
  unless missing.isEmpty do
    return (#[s!"{root}: the closure lacks the literal support {missing}"], #[])
  match Ix.LeanIngress.checkSourceBundled sub (Ix.Cert.blocksOf sub) with
  | .error e => return (#[s!"{root}: the closure ({sub.consts.size} constants) is declined: {e}"], #[])
  | .ok envS =>
    return (#[], #[s!"{root}: statement closure {sub.consts.size} constants, {literal.length} with a \
      string literal, all {support.size} support constants; Source at the bundle evidence accepts it \
      ({envS.consts.length} kernel constants)"])

def report (name : String) (action : IO (Array String × Array String)) (count : Nat) : TestSeq :=
  .individualIO name none (do
    let (errors, lines) ← action
    for l in lines do IO.println l
    let msg := if errors.isEmpty then none else some ("\n".intercalate errors.toList)
    return (errors.isEmpty, count, 0, msg)) .done

def suite : List TestSeq := [
  report "Ix.Cert.compile against the IO pipeline and the Rust compiler, on the fixtures" (do
    let leanEnv ← getCompileEnv #[defsModule, ownModule]
    parity "fixtures" (← fixtureConsts leanEnv) 4) 1,
  report "the statements' hypotheses and conclusion, per root, on the accepted fixtures" (do
    perRoot (← getCompileEnv #[defsModule, ownModule])) 1,
  report "binder contracts on both sides, on the resolved source-contract syntax fixtures" (do
    contractAgreement (← getCompileEnv #[syntaxModule])) 1,
  report "the shipped role table's certificates check on their pinned closure (Route A, B6b)"
    roleEvidenceCase 1,
  report "a closure with a well-founded Nat operation, at the bundle evidence (Nat.div)" (do
    natDivClosure (← getCompileEnv #[defsModule, ownModule])) 1,
  report "a closure with a string literal holds its literal support (outOfBounds)" (do
    literalClosure (← getCompileEnv #[defsModule, ownModule]) `outOfBounds) 1]

/-- `cert-compile-parity-init` (ignored): the parity on `Init`. -/
def initSuite : List TestSeq := [
  report "Ix.Cert.compile against the IO pipeline and the Rust compiler, on Init" (do
    let leanEnv ← getCompileEnv #[`Init]
    parity "Init" leanEnv.constants.toList 6) 1]

/-- `cert-roles-initstd` (ignored): the role table's bindings (Route A, B5a) on Init+Std,
compiled in process by the Rust compiler (byte-identical to `Ix.Cert.compile`'s, the
gates' byte leg `46214545…`). -/
def rolesInitStdSuite : List TestSeq := [
  report "the role table's bindings in the compiled Init+Std (Route A, B5a)" (do
    let leanEnv ← getCompileEnv #[`Init, `Std]
    let env ← IO.lazyPure fun _ =>
      Tests.Ix.Kernel.SourceIngressStep.canon leanEnv.constants.toList.toArray 16
    let dir ← IO.FS.createTempDir
    let ixe ← try
        let path := dir / "initstd.ixe"
        let _ ← Ix.CompileM.rsCompileEnvBytes leanEnv path.toString
        IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
      finally IO.FS.removeDirAll dir
    rolesCases "Init+Std" env ixe) 1]

/-- `cert-noctor-initstd` (ignored): N-READS N4 (a)'s premise `NoCtorIn` on every inductive of
Init+Std. -/
def noCtorInitStdSuite : List TestSeq := [
  report "no constructor of a family in its types, on Init+Std (N-READS N4 a)" (do
    let leanEnv ← getCompileEnv #[`Init, `Std]
    let env ← IO.lazyPure fun _ =>
      Tests.Ix.Kernel.SourceIngressStep.canon leanEnv.constants.toList.toArray 16
    noCtorCases "Init+Std" env) 1]


/-- `cert-unchanged`: B9a on the aux-heavy fixture corpus (`validateAuxClosure`, the
`changed-set` corpus, which has changed components), compiled by `Ix.Cert.compileReport` (`compileUnchecked`, then `checkReport`: the final
compile environment gives the aux table). -/
def unchangedCorpus (leanEnv : Lean.Environment) : IO UInt32 := do
  let filtered := validateAuxClosure leanEnv
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon filtered.toArray 8
  -- `compileReport`, with the final compile environment for the aux table
  let (ixe, failures, cenv) ← IO.ofExcept (← IO.lazyPure fun _ => Ix.Cert.compileUnchecked env)
  IO.ofExcept (Ix.Cert.checkReport env cenv (ixe, failures))
  IO.println s!"[cert-unchanged] corpus: {filtered.length} constants, {failures.toMap.size} failures"
  let (errors, lines) := unchangedCases "corpus" env (Ix.Cert.compileBlocks env) cenv.auxReport.table ixe
  for l in lines do IO.println s!"[cert-unchanged] {l}"
  for e in errors do IO.eprintln s!"[cert-unchanged] FAIL {e}"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Cert.Statement
