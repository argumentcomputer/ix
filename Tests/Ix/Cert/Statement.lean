import LSpec
import Ix.Meta
import Ix.Cert.Audit
import Tests.Ix.Kernel.SourceIngress
import Tests.Ix.SourceContract.SyntaxFixture
import Ix.Ixon.CheckOrder

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
resolution map at the end of the fold (from `Ix.Cert.compileUnchecked`'s third
component), which the resolution and publication checks read. -/
def checkReportCases (label : String) (env : Ix.Environment) (ixe : Ixon.Env)
    (failures : Ix.Cert.Failures) (cenv : Ix.CompileM.CompileEnv) :
    IO (Array String × Array String) := do
  let resolved := cenv.nameToAddr
  -- `checkReport` on the driver's final environment with its resolution map
  -- replaced (the planted cases)
  let chk := fun (r : Std.HashMap Ix.Compile.ExactKey.ExactName Address) (out : Ixon.Env × Ix.Cert.Failures) =>
    Ix.Cert.checkReport env { cenv with nameToAddr := r } out
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
    match chk resolved (ixe', failures') with
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
  match chk resolved ({ ixe with named := ixe.named.insert twin named }, failures) with
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
      match chk resolved ({ ixe with named := ixe.named.insert entry planted }, failures) with
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
  -- name's entry moved off its resolved address (as a later block's `Muts` entry
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
      match chk resolved' (ixe', failures) with
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
    match chk resolved ({ ixe with named := dropped }, failures) with
    | .error e =>
      if (e.splitOn "component check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a block's Muts entry dropped by the \
          component check ({ixe.named.size - dropped.size} entries dropped)"
      else
        errors := errors.push s!"{label}: the dropped Muts entry is refused, but not by the component check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a block's Muts entry dropped"
  -- the publication check (every published input name resolved), timed alone
  -- on the compile's result, then refusing, by its own message, the result with
  -- a published input name dropped from the resolution map
  let p0 ← IO.monoMsNow
  let unresolved? ← IO.lazyPure fun _ => Ix.Cert.unresolvedPublished env resolved ixe
  let p1 ← IO.monoMsNow
  match unresolved? with
  | none => lines := lines.push s!"{label}: unresolvedPublished finds every published input name \
      resolved ({ixe.named.size} published names, {p1 - p0} ms)"
  | some n => errors := errors.push s!"{label}: unresolvedPublished finds {n.pretty} in the compile's result"
  let droppable := env.consts.toList.findSome? fun (n, _) =>
    if ixe.named.contains n && resolved.contains n then some n else none
  match droppable with
  | none => errors := errors.push s!"{label}: no published, resolved input name"
  | some n =>
    match chk (resolved.erase n) (ixe, failures) with
    | .error e =>
      if (e.splitOn "publication check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a published input name dropped from \
          the resolution map ({n.pretty})"
      else
        errors := errors.push s!"{label}: the dropped published name is refused, but not by the \
          publication check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a published input name \
        that is not resolved"
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
  -- and the input with one definition whose own name is a respelling of the
  -- name it is stored under that shares its stored hash (`==` cannot tell them
  -- apart; the exact spelling can)
  match defs with
  | (n, .defnInfo v) :: _ =>
    let respelled : Ix.Name := .str n "respelled" n.getHash
    let ci' : Ix.ConstantInfo := .defnInfo { v with cnst := { v.cnst with name := respelled } }
    let env' : Ix.Environment := { env with consts := env.consts.insert n ci' }
    match Ix.Cert.checkReport env' cenv (ixe, failures) with
    | .error e =>
      if (e.splitOn "name invariant failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses an input definition whose own name is a \
          hash-equal respelling of its stored name ({n.pretty})"
      else
        errors := errors.push s!"{label}: the respelled input is refused, but not by the name \
          invariant: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a respelled own name"
  | _ => errors := errors.push s!"{label}: no input definition"
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
  -- the projection check (one stored definition projection record per member),
  -- timed alone, then refusing, by its own message, a second authentic record
  -- projecting a member (an existing projection with its univs grown, stored at
  -- the admission hash of its bytes)
  let p0 ← IO.monoMsNow
  let projC? ← IO.lazyPure fun _ => Ix.Cert.projectionCollision ixe
  let p1 ← IO.monoMsNow
  match projC? with
  | none => lines := lines.push s!"{label}: projectionCollision finds one projection record per \
      definition member ({ixe.consts.size} records, {p1 - p0} ms)"
  | some (b, i) => errors := errors.push s!"{label}: projectionCollision finds member {i} of {b} \
      projected twice"
  let projected : Option Ixon.Constant := ixe.consts.toList.findSome? fun (a, lc) =>
    match Ix.Cert.definitionProjection (a, lc), lc.get? with
    | some _, some c => some c
    | _, _ => none
  match projected with
  | some c =>
    let bytes := Ixon.ser { c with univs := c.univs.push .zero }
    let consts' := ixe.consts.insert (Address.admissionHash bytes) (Ixon.LazyConstant.ofSlice bytes 0 bytes.size)
    let ixeP : Ixon.Env := { ixe with consts := consts' }
    match Ix.Cert.checkReport env cenv (ixeP, failures) with
    | .error e =>
      if (e.splitOn "projection check failed").length > 1 then
        lines := lines.push s!"{label}: checkReport refuses a second stored projection record of a \
          definition member"
      else
        errors := errors.push s!"{label}: the second projection record is refused, but not by the \
          projection check: {e}"
    | .ok () => errors := errors.push s!"{label}: checkReport accepts a second projection record of a \
        definition member"
  | none => lines := lines.push s!"{label}: no definition projection record to plant a second of"
  -- the readability check (every published input name at a stored record that
  -- is not a block), timed alone on the compile's result, then refusing, by its
  -- own message, a published input name moved, with its resolution, to a block's
  -- address and to an unstored address (a name no `Muts` class lists, no
  -- inductive and no head, so no earlier check sees it)
  let u0 ← IO.monoMsNow
  let unreadable? ← IO.lazyPure fun _ => Ix.Cert.unreadablePublished env ixe
  let u1 ← IO.monoMsNow
  match unreadable? with
  | none => lines := lines.push s!"{label}: unreadablePublished finds every published input name \
      at a stored record that is not a block ({ixe.named.size} published names, {u1 - u0} ms)"
  | some n => errors := errors.push s!"{label}: unreadablePublished finds {n.pretty} in the \
      compile's result"
  let inMuts : Std.HashSet Address := entries.foldl (init := {}) fun s (_, nd) =>
    match nd.constMeta.info with
    | .muts all _ => all.foldl (init := s) fun s cls => cls.foldl (·.insert ·) s
    | _ => s
  let blockAddr? := entries.head?.map (·.2.addr)
  let movable := resolved.toList.find? fun (k, _) =>
    ixe.named.contains k && env.consts.contains k && !inMuts.contains (Ix.Name.getHash k) &&
      !(env.consts.get? k matches some (.inductInfo _))
  match blockAddr?, movable with
  | some blockAddr, some (k, _) =>
    let some nd := ixe.named.get? k
      | return (errors.push s!"{label}: a published resolved name has no entry", lines)
    let unstored := Address.blake3Pure "planted-unstored-record".toUTF8
    let mut byCheck := 0
    for (what, addr) in [("at a block's address", blockAddr), ("at an unstored address", unstored)] do
      let ixe' := { ixe with named := ixe.named.insert k { nd with addr := addr } }
      if Ix.Cert.unreadablePublished env ixe' != some k then
        errors := errors.push s!"{label}: unreadablePublished misses an input name published {what}"
      match chk (resolved.insert k addr) (ixe', failures) with
      | .error e =>
        if (e.splitOn "readability check failed").length > 1 then byCheck := byCheck + 1
        else errors := errors.push s!"{label}: an input name published {what} is refused, but not by \
          the readability check: {e}"
      | .ok () => errors := errors.push s!"{label}: checkReport accepts an input name published {what}"
    lines := lines.push s!"{label}: checkReport refuses {byCheck} of 2 unreadable publications by the \
      readability check"
  | _, _ => errors := errors.push s!"{label}: no Muts entry, or no movable published input name, to \
      plant an unreadable publication with"
  -- the blob check (no address holds both a stored blob and a stored record),
  -- timed alone on the compile's result, then refusing, by its own message, a
  -- blob stored at a record's address with the record's bytes (what a literal
  -- whose bytes are that record's serialization stores)
  let bl0 ← IO.monoMsNow
  let blobRecord? ← IO.lazyPure fun _ => Ix.Cert.blobRecordCollision ixe
  let bl1 ← IO.monoMsNow
  match blobRecord? with
  | none => lines := lines.push s!"{label}: blobRecordCollision finds no address holding both a \
      blob and a record ({ixe.blobs.size} blobs, {bl1 - bl0} ms)"
  | some a => errors := errors.push s!"{label}: blobRecordCollision finds {a} in the compile's result"
  match chk resolved ({ ixe with blobs := ixe.blobs.insert a₁ lc₁.rawBytes }, failures) with
  | .error e =>
    if (e.splitOn "blob check failed").length > 1 then
      lines := lines.push s!"{label}: checkReport refuses a blob stored at a record's address with \
        the record's bytes"
    else
      errors := errors.push s!"{label}: the planted blob is refused, but not by the blob check: {e}"
  | .ok () => errors := errors.push s!"{label}: checkReport accepts a blob stored at a record's address"
  -- the recursor check (every input name published in an inductive block the index
  -- attaches recursors to has a family, of which each of those recursors is a
  -- published recursor), timed alone on the compile's result, then refusing, by its
  -- own message, an input recursor indexed under its family's block, the family's
  -- only one, whose `all` is rewritten to name another input inductive: a recursor
  -- with `all = [J]` in `I`'s motive slot
  let rc0 ← IO.monoMsNow
  let unowned? ← IO.lazyPure fun _ => Ix.Cert.unownedRecursor env ixe
  let rc1 ← IO.monoMsNow
  let idx := Ix.Kernel.Reader.buildIndex (Ix.Cert.storedRecord ixe) (Ix.Cert.storedRecursorRecords ixe)
  match unowned? with
  | none => lines := lines.push s!"{label}: unownedRecursor finds every indexed recursor published \
      for its block's family ({idx.blocks.size} indexed blocks, {rc1 - rc0} ms)"
  | some (b, x, none) => errors := errors.push s!"{label}: unownedRecursor finds {x.pretty}, \
      published in the indexed block {b}, without a family in the compile's result"
  | some (b, x, some r) => errors := errors.push s!"{label}: unownedRecursor finds the recursor \
      record {r.block} under the block {b} not published for the family of {x.pretty} in the \
      compile's result"
  let indexed : Std.HashSet Address := idx.blocks.fold (init := {}) fun s _ shape =>
    shape.recs.foldl (fun s r => s.insert r.block) s
  let familySize : Std.HashMap Address Nat := env.consts.fold (init := {}) fun m _ ci =>
    match ci with
    | .recInfo rv =>
      match rv.all[0]? with
      | some f => m.insert f.getHash (m.getD f.getHash 0 + 1)
      | none => m
    | _ => m
  let target := env.consts.toList.findSome? fun (rn, ci) =>
    match ci with
    | .recInfo rv =>
      match rv.all[0]? with
      | some f =>
        if (Ix.Cert.publishedRecords ixe rn).any indexed.contains && familySize.getD f.getHash 0 == 1 then
          some (rn, rv, f)
        else none
      | none => none
    | _ => none
  match target with
  | some (rn, rv, f) =>
    let other := env.consts.toList.findSome? fun (n, ci) =>
      match ci with
      | .inductInfo iv => if (iv.all[0]?.map (·.getHash)) != some f.getHash then some n else none
      | _ => none
    match other with
    | some j =>
      let env' : Ix.Environment :=
        { env with consts := env.consts.insert rn (.recInfo { rv with all := #[j] }) }
      match Ix.Cert.checkReport env' cenv (ixe, failures) with
      | .error e =>
        if (e.splitOn "recursor check failed").length > 1 then
          lines := lines.push s!"{label}: checkReport refuses the recursor {rn.pretty} of an indexed \
            block with its `all` rewritten to [{j.pretty}]"
        else
          errors := errors.push s!"{label}: the rewritten recursor {rn.pretty} is refused, but not by \
            the recursor check: {e}"
      | .ok () => errors := errors.push s!"{label}: checkReport accepts the recursor {rn.pretty} of an \
          indexed block with its `all` rewritten to [{j.pretty}]"
    | none => errors := errors.push s!"{label}: no input inductive of another family to rewrite a \
        recursor's `all` to"
  | none => errors := errors.push s!"{label}: no indexed input recursor alone in its family to rewrite"
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

/-- The default role table, decoded once. -/
def defaultTable? : Option Ix.Kernel.RoleTable := Ix.Kernel.Reader.defaultTable.toOption

/-- What the closure's steps read off the whole artifact, computed once: its recursor
index (`Ix.Cert.artifactRecIndex`) and the certificate ground of each `Nat` operation,
under the default table, at the operation's bound record and at the block that holds it. -/
structure ClosureCx where
  idx : Ix.Kernel.Reader.RecIndex
  ground : Std.HashMap Address (Array Address)

/-- The artifact's addresses of the roles `rs`, under the default table. -/
def roleTargets (ixe : Ixon.Env) (rs : List Ix.Kernel.Role) : Array Address :=
  match defaultTable? with
  | none => #[]
  | some t => (rs.filterMap t.addressOf?).toArray.filter (ixe.consts.contains ·)

def ClosureCx.of (ixe : Ixon.Env) : ClosureCx :=
  let ground := match defaultTable? with
    | none => {}
    | some t => t.bound.foldl (init := ({} : Std.HashMap Address (Array Address))) fun m (r, p) =>
      let ts := roleTargets ixe (Ix.Cert.groundRoles r)
      if ts.isEmpty then m else
        let m := m.insert p (m.getD p #[] ++ ts)
        match Ix.Cert.recordAt ixe p with
        | some c =>
          let o := Ix.Cert.ownerOf p c
          if o != p then m.insert o (m.getD o #[] ++ ts) else m
        | none => m
  ⟨Ix.Cert.artifactRecIndex ixe, ground⟩

/-- The records the fold reads at the record `a` (decoded `c`, if stored) without a
reference (`Ix.Cert.GroundEdge`), under the default table: the certificate ground of a
`Nat` operation bound at `a` or at a projection whose block is `a`, and the support of
`a`'s literals, wherever the artifact stores them. -/
def groundTargets (ixe : Ixon.Env) (cx : ClosureCx) (a : Address) (c : Option Ixon.Constant) :
    Array Address :=
  cx.ground.getD a #[] ++ ((c.map Ix.Cert.literalRoles).map (roleTargets ixe)).getD #[]

/-- The records a record needs before it (`Ix.Cert.CompiledReach`'s steps but the
recursors'): its block, for a projection, the records of its reference table
(`Ix.Cert.RecordEdge`), and the records the fold reads without a reference
(`groundTargets`). -/
def edges (ixe : Ixon.Env) (cx : ClosureCx) (a : Address) : Array Address :=
  match Ix.Cert.recordAt ixe a with
  | none => groundTargets ixe cx a none
  | some c =>
    let o := Ix.Cert.ownerOf a c
    (if o != a then #[o] else #[]) ++ c.refs.filter (ixe.consts.contains ·) ++
      groundTargets ixe cx a (some c)

/-- The recursor records of the inductive block at `a` (`Ix.Cert.RecursorEdge`, over the
artifact's index). A recursor references its block, so it comes after it. -/
def recursorTargets (ixe : Ixon.Env) (cx : ClosureCx) (a : Address) : Array Address :=
  ((cx.idx.blocks[a]?.map (·.recs)).getD #[]).filterMap fun r =>
    if r.block != a && ixe.consts.contains r.block then some r.block else none

/-- The compiled closure of `seeds`, dependencies first: a depth-first postorder over
`edges` from each seed, then from the recursors of every block it emits. A record is
expanded once. -/
def closureOrder (ixe : Ixon.Env) (seeds : Array Address) : Array Address := Id.run do
  let cx := ClosureCx.of ixe
  let mut expanded : Std.HashSet Address := {}
  let mut done : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  let mut roots : Array Address := seeds
  let mut i := 0
  while h : i < roots.size do
    let root := roots[i]
    i := i + 1
    unless ixe.consts.contains root do continue
    let mut stack : Array (Address × Bool) := #[(root, false)]
    while h : stack.size > 0 do
      let (node, post) := stack[stack.size - 1]
      stack := stack.pop
      if post then
        unless done.contains node do
          done := done.insert node
          out := out.push node
          roots := roots ++ recursorTargets ixe cx node
      else unless expanded.contains node do
        expanded := expanded.insert node
        stack := stack.push (node, true)
        for d in edges ixe cx node do
          unless expanded.contains d do stack := stack.push (d, false)
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
def reach (ixe : Ixon.Env) (seeds : Array Address) (cx : ClosureCx := ClosureCx.of ixe) :
    Std.HashSet Address := Id.run do
  let mut seen : Std.HashSet Address := {}
  let mut todo := seeds.filter (ixe.consts.contains ·)
  while h : todo.size > 0 do
    let a := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains a then continue
    seen := seen.insert a
    todo := todo ++ edges ixe cx a ++ recursorTargets ixe cx a
  return seen

/-- **The ground step against the executable check order's edges**: over the compiled
closure of `seeds`, the blocks the statement's ground step reaches from each block
(`groundTargets`, `Ix.Cert.GroundEdge`) are the blocks the check order's extra edges give
it (`Ixon.CheckOrder.groundEdges` and `Ix.Kernel.Reader.literalEdges`, over the reader's
bindings of the default table). -/
def groundEdgeCases (label : String) (ixe : Ixon.Env) (seeds : Array Address) :
    Array String × Array String := Id.run do
  let some t := defaultTable? | return (#[s!"{label}: the default role table does not read"], #[])
  let .ok (pre : Ix.Kernel.Reader.Prelude .anon) := Ix.Kernel.Reader.preludeFor t
    | return (#[s!"{label}: the committed prelude does not read"], #[])
  let all := Ix.Cert.storedRecords ixe
  let cx := Ix.Kernel.Admission.streamContext Address.admissionHash t pre all.toList ixe.blobs.toList
    (Ix.Cert.hintsOf ixe)
  let extra := Ixon.CheckOrder.mergeEdges (Ixon.CheckOrder.groundEdges cx.roles.names)
    (Ix.Kernel.Reader.literalEdges cx.roles.names all)
  let owner (a : Address) : Address := ((Ix.Cert.recordAt ixe a).map (Ix.Cert.ownerOf a)).getD a
  let closureCx := ClosureCx.of ixe
  let reached := reach ixe seeds closureCx
  -- the statement's ground step, by block
  let mut ours : Std.HashMap Address (Std.HashSet Address) := {}
  let mut owners : Std.HashSet Address := {}
  for a in reached.toList do
    let c := Ix.Cert.recordAt ixe a
    let o := (c.map (Ix.Cert.ownerOf a)).getD a
    owners := owners.insert o
    let ts := (groundTargets ixe closureCx a c).map owner |>.filter (· != o)
    ours := ours.insert o (ts.foldl (·.insert ·) (ours.getD o {}))
  let mut differ : Array Address := #[]
  let mut edgesSeen := 0
  for o in owners.toList do
    let mine := ours.getD o {}
    let theirs := ((extra.getD o #[]).filter (· != o)).foldl (·.insert ·) ({} : Std.HashSet Address)
    edgesSeen := edgesSeen + theirs.size
    unless mine.size == theirs.size && mine.toList.all theirs.contains do
      differ := differ.push o
  if differ.isEmpty then
    return (#[], #[s!"{label}: the ground step agrees with the check order's ground and \
      literal edges on {reached.size} records ({edgesSeen} edges)"])
  else
    return (#[s!"{label}: the ground step and the check order's extra edges differ at \
      {differ.size} blocks: {differ.toList.take 5}"], #[])

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
  let (groundErrors, groundLines) := groundEdgeCases "closure" ixe seeds
  errors := errors ++ groundErrors
  lines := lines ++ groundLines
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
  -- the committed fallback rows at the hashes of their bytes, timed alone on rows read at
  -- run time (`fallbackHashed` is a closed constant, computed once when the module loads)
  let rows ← IO.lazyPure fun _ => Ix.Kernel.Reader.RoleData.prelude ++ Ix.Kernel.Reader.RoleData.evidence
  let f0 ← IO.monoMsNow
  let hashed ← IO.lazyPure fun _ => rows.all fun row =>
    (bytesOfHex row.2).map Address.admissionHash == Ix.Kernel.Reader.addressOfHex row.1
  let f1 ← IO.monoMsNow
  unless hashed == Ix.Cert.RoleClosure.fallbackHashed do
    return (#[s!"role evidence: the timed fallback hashes disagree with fallbackHashed"], #[])
  unless hashed do
    return (#[s!"role evidence: a committed prelude or evidence row is not stored at the hash of its bytes"], #[])
  let hashedLine := s!"role evidence: the {Ix.Kernel.Reader.RoleData.prelude.size + Ix.Kernel.Reader.RoleData.evidence.size} committed \
    fallback rows sit at the hashes of their bytes ({f1 - f0} ms)"
  -- the default binding admitted under the admission hash, timed alone on the binding read
  -- at run time (`defaultAdmits` is a closed constant too)
  let binding ← IO.lazyPure fun _ => Ix.Kernel.Admission.defaultBinding
  let a0 ← IO.monoMsNow
  let admits ← IO.lazyPure fun _ => Ix.Cert.RoleClosure.admitsOf binding
  let a1 ← IO.monoMsNow
  unless admits == Ix.Cert.RoleClosure.defaultAdmits do
    return (#[s!"role evidence: the timed admission disagrees with defaultAdmits"], #[])
  unless admits do
    return (#[s!"role evidence: the default binding does not admit under the admission hash"], #[])
  let admitsLine := s!"role evidence: the default binding admits under the admission hash ({a1 - a0} ms)"
  -- the committed prelude read at both modes, names erased, timed alone on the table read at
  -- run time (`preludeAgrees` is a closed constant too)
  let table ← IO.lazyPure fun _ => Ix.Kernel.Reader.defaultTable
  let p0 ← IO.monoMsNow
  let agrees ← IO.lazyPure fun _ => Ix.Cert.RoleClosure.preludeAgreesOf table
  let p1 ← IO.monoMsNow
  unless agrees == Ix.Cert.RoleClosure.preludeAgrees do
    return (#[s!"role evidence: the timed prelude agreement disagrees with preludeAgrees"], #[])
  unless agrees do
    return (#[s!"role evidence: the committed prelude does not read alike at both modes"], #[])
  let agreesLine := s!"role evidence: the committed prelude reads alike at both modes, names erased ({p1 - p0} ms)"
  match Ix.Cert.RoleClosure.preparedDefault with
  | .error e => return (#[s!"the committed role closure does not prepare: {e}"], #[])
  | .ok (ev, ds) =>
    if Ix.Cert.RoleClosure.roleEvidenceCheck then
      return (#[], #[hashedLine, admitsLine, agreesLine, s!"role evidence: the pinned closure ({ds.length} declarations, \
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

/-- The roles of the well-founded `Nat` operations (`Ix.Kernel.natDivModNames`). -/
def wellFoundedRoles : List Ix.Kernel.Role :=
  [.natDiv, .natMod, .natGcd, .natLand, .natLor, .natXor, .natShiftLeft, .natShiftRight]

/-- The roles of the structural `Nat` operations (`Ix.Kernel.natOpNames`). -/
def structuralRoles : List Ix.Kernel.Role :=
  [.natPred, .natAdd, .natSub, .natMul, .natPow, .natBeq, .natBle]

/-- **The role table's evidence against quotient Source's**, on the compiled closure of
the well-founded `Nat` operations: the evidence the certified reader resolves from the
default table in the closure's reading (`Ix.Kernel.Reader.evidenceOf`, through
`Ix.Kernel.Admission.readStream`) against the bundle's evidence renamed onto the
representatives and then to the artifact's addresses (`Ix.Cert.sourceEvidence`,
`Ix.LeanIngress.evAddr`), compared where the fold's gates read them: a structural
operation's `defeq` shape (`evidenceDefeqOk`) and a well-founded operation's proof terms
(`evidenceProofs`; the theorems' keys are not read). Asserted: every structural operation's
shape passes on both sides, every well-founded operation's proof terms are equal, and the
renamed run is accepted at both. Quotient Source's bundle is the table's own evidence records
read by name (`kernel-pin-gen --quotient-names`), so a drift between the two fails here. -/
def evidenceAgreement (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let roots : Array Lean.Name :=
    #[`Nat.div, `Nat.mod, `Nat.gcd, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft, `Nat.shiftRight]
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv roots)
  let prepared ← IO.ofExcept (Ix.Compile.prepareRegisteredConstants leanEnv closed)
  let env := Tests.Ix.Kernel.SourceIngressStep.canon prepared.toArray
  let sub := Ix.Cert.closure env (roots.toList.map Ix.Name.fromLeanName)
  let ixe ← match Ix.Cert.compile env with
    | .ok ixe => pure ixe
    | .error e => return (#[s!"evidence: the closure does not compile: {e}"], #[])
  let some t := defaultTable? | return (#["evidence: the default role table does not read"], #[])
  let .ok binding := Ix.Kernel.Admission.defaultBinding
    | return (#["evidence: the default binding does not load"], #[])
  let .ok tA := Ix.Kernel.Admission.admitBinding Address.admissionHash binding
    | return (#["evidence: the default binding does not admit"], #[])
  let .ok (preA : Ix.Kernel.Reader.Prelude .anon) := Ix.Kernel.Reader.preludeFor tA
    | return (#["evidence: the committed prelude does not read"], #[])
  let .ok b := Ix.RoleEvidence.quotientBundle ()
    | return (#["evidence: the committed bundle does not load"], #[])
  let seeds : Array Address := sub.consts.toArray.filterMap fun (n, _) => (ixe.named.get? n).map (·.addr)
  let order := (closureOrder ixe seeds).toList
  let read := Ix.Kernel.Admission.readStream Address.admissionHash tA preA (Ix.Cert.Stream.decodedOf ixe order)
    (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe)
  let .ok (evR, _) := read | return (#[s!"evidence: the compiled closure does not read"], #[])
  let evB := (Ix.Cert.sourceEvidence ixe t).mapKeys (Ix.LeanIngress.evAddr ixe b)
  let byAddr : Std.HashMap Address Ix.Name := ixe.named.fold (fun m n d => m.insert d.addr n) {}
  let keyName (k : Ix.Kernel.Key .anon) : String := match k with
    | .id a => ((byAddr.get? a).map toString).getD s!"{a}"
    | k => s!"{k}"
  let mut errors : Array String := #[]
  let mut lines : Array String := #[]
  lines := lines.push s!"evidence: the well-founded operations' closure: {sub.consts.size} constants, \
    {order.length} records read"
  -- the renamed quotient Source run under each evidence (the transfer's conclusion, executed)
  match Ix.Kernel.Reader.builtinPrelude (md := .source) with
  | .error e => errors := errors.push s!"evidence: the Source prelude does not read: {e}"
  | .ok pre =>
    match Ix.LeanIngress.prepareSourceCollapsedAt ixe t ((Ix.LeanIngress.fiberHintsMap ixe)[·]?) pre sub
        (Ix.Cert.blocksOf sub) with
    | .error e => errors := errors.push s!"evidence: quotient Source does not prepare the closure: {e}"
    | .ok ds =>
      let renamed := ds.map (Ix.Kernel.Declaration.mapKeys (Ix.LeanIngress.evAddr ixe b))
      let verdict (ev : Ix.Kernel.Evidences .anon) : Option String :=
        match Ix.Kernel.Cached.checkDecls .verified ev renamed with
        | .ok _ => none
        | .error (e, i) => some s!"declines at {i}: {e}"
      let say (v : Option String) : String := v.getD "accepts"
      lines := lines.push s!"evidence: the renamed quotient Source run ({renamed.size} declarations): \
        at the bundle's evidence it {say (verdict evB)}; at the table's it {say (verdict evR)}"
      for (side, ev) in [("bundle's", evB), ("table's", evR)] do
        if let some why := verdict ev then
          errors := errors.push s!"evidence: the renamed quotient Source run at the {side} evidence {why}"
  for r in structuralRoles do
    let k : Ix.Kernel.Key .anon := Ix.Kernel.roleKey r
    let okR := Ix.Kernel.evidenceDefeqOk evR k
    let okB := Ix.Kernel.evidenceDefeqOk evB k
    lines := lines.push s!"evidence: {repr r}: defeq shape, table {okR}, bundle {okB}"
    unless okR && okB do errors := errors.push s!"evidence: {repr r}: the defeq shape, table {okR}, \
      bundle {okB}"
  for r in wellFoundedRoles do
    let k : Ix.Kernel.Key .anon := Ix.Kernel.roleKey r
    match Ix.Kernel.evidenceProofs evR k, Ix.Kernel.evidenceProofs evB k with
    | some ps, some qs =>
      if ps == qs then
        lines := lines.push s!"evidence: {repr r}: {ps.length} proofs, equal"
      else
        let pairs := ps.zip qs
        let same := (pairs.filter fun (p, q) => p == q).length
        let keys (e : Ix.Kernel.Expr .anon) : List (Ix.Kernel.Key .anon) := e.constKeyList.eraseDups
        let diffs := pairs.filterMap fun (p, q) =>
          if p == q then none else
            let kp := keys p
            let kq := keys q
            some s!"[table-only keys {((kp.filter (!kq.contains ·)).take 4).map keyName}, \
              bundle-only keys {((kq.filter (!kp.contains ·)).take 4).map keyName}]"
        errors := errors.push s!"evidence: {repr r}: table {ps.length} proofs, bundle {qs.length}; \
          {same} equal; differing: {diffs.take 2}"
    | none, some qs =>
      errors := errors.push s!"evidence: {repr r}: the table's evidence resolves no proofs; the bundle has \
        {qs.length}"
    | some ps, none =>
      errors := errors.push s!"evidence: {repr r}: the bundle's evidence has no proofs; the table resolves \
        {ps.length}"
    | none, none => errors := errors.push s!"evidence: {repr r}: no proofs on either side"
  -- the evidence check (part of the artifact checks) on the closure's artifact
  let started ← IO.monoMsNow
  let checked ← IO.lazyPure fun _ => Ix.Cert.EvidenceCheck.evidenceCheck t ixe
  match checked with
  | .ok () => lines := lines.push s!"evidence: the evidence check passes on the closure's artifact \
      ({(← IO.monoMsNow) - started} ms)"
  | .error e => errors := errors.push s!"evidence: the evidence check refuses the closure's artifact: {e}"
  -- and on the artifact of a closure that holds no well-founded operation
  match Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[`List.length] with
  | .error e => errors := errors.push s!"evidence: the closure of `List.length` does not compute: {e}"
  | .ok closedSmall =>
    match Ix.Compile.prepareRegisteredConstants leanEnv closedSmall with
    | .error e => errors := errors.push s!"evidence: the closure of `List.length` does not prepare: {e}"
    | .ok preparedSmall =>
      let envSmall := Tests.Ix.Kernel.SourceIngressStep.canon preparedSmall.toArray
      match Ix.Cert.compile envSmall with
      | .error e => errors := errors.push s!"evidence: the closure of `List.length` does not compile: {e}"
      | .ok ixeSmall =>
        match Ix.Cert.EvidenceCheck.evidenceCheck t ixeSmall with
        | .ok () => lines := lines.push s!"evidence: the evidence check passes on the artifact of `List.length`'s \
            closure ({ixeSmall.consts.size} records), which holds no well-founded operation"
        | .error e => errors := errors.push s!"evidence: the evidence check refuses the artifact of `List.length`'s \
            closure: {e}"
  return (errors, lines)

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

/-- **An axiom α-equal to `sorryAx` is represented by `sorryAx`'s role.** A copy of
`sorryAx` under another name compiles to `sorryAx`'s record, so the artifact
publishes it at `sorryAx`'s address, and quotient Source keys it by `sorryAx`'s role
(`Ix.Cert.quotientKey`), whose declaration installs nothing. The coverage statements
therefore leave out every constant whose quotient key is that role, not only
`sorryAx` itself. -/
def sorryAliasCase (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let some (.axiomInfo sv) := leanEnv.find? ``sorryAx
    | return (#["sorryAx alias: sorryAx is not an axiom of the test environment"], #[])
  let aliasName : Lean.Name := `Tests.Ix.Cert.Statement.sorryAlias
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[``sorryAx])
  let consts := closed ++ [(aliasName, .axiomInfo { sv with name := aliasName })]
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts.toArray 2
  let (ixe, _) ← match Ix.Cert.compileReport env with
    | .ok out => pure out
    | .error e => return (#[s!"sorryAx alias: compileReport failed: {e}"], #[])
  let t ← match Ix.Kernel.Reader.defaultTable with
    | .ok t => pure t
    | .error e => return (#[s!"sorryAx alias: the default role table failed: {e}"], #[])
  let sorryN := Ix.Name.fromLeanName ``sorryAx
  let aliasN := Ix.Name.fromLeanName aliasName
  let addr (n : Ix.Name) : Option Address := (ixe.named.get? n).map (·.addr)
  let mut errors : Array String := #[]
  match addr sorryN, addr aliasN with
  | some a, some b =>
    unless a == b do
      errors := errors.push s!"sorryAx alias: published at {b}, sorryAx at {a}"
  | _, _ => errors := errors.push "sorryAx alias: sorryAx and its alias are not both published"
  let key := Ix.Cert.quotientKey ixe t aliasN
  unless key == Ix.Kernel.sorryAxName do
    errors := errors.push s!"sorryAx alias: its quotient key is {key}, not sorryAx's role"
  if errors.isEmpty then
    return (#[], #[s!"sorryAx alias: published at sorryAx's address ({consts.length} constants), \
      quotient key {key}"])
  return (errors, #[])

/-- **A literal whose bytes are a record's serialization is refused** by
`compileReport`'s blob check: a target axiom compiles alone to a record `R`,
and a definition whose value is the `Nat` literal with `R`'s serialization as
its little-endian bytes stores a blob at `R`'s address beside `R` itself. The
first candidate target whose record does not end with a zero byte is used,
so that the literal's bytes are exactly the record's. -/
def blobRecordCase : IO (Array String × Array String) := do
  let target : Lean.Name := `Tests.Ix.Cert.Statement.blobTarget
  let literal : Lean.Name := `Tests.Ix.Cert.Statement.blobLiteral
  -- `Sort u` first: its universe table ends with a parameter, whose tag byte is nonzero
  for (params, lvl) in [([`u], Lean.Level.param `u), ([], Lean.Level.succ .zero)] do
    let targetC : Lean.ConstantInfo :=
      .axiomInfo { name := target, levelParams := params, type := .sort lvl, isUnsafe := false }
    let alone ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon #[(target, targetC)]
    let (ixe₀, _) ← match Ix.Cert.compileReport alone with
      | .ok out => pure out
      | .error e => return (#[s!"blob/record: the target alone failed to compile: {e}"], #[])
    let some named := ixe₀.named.get? (Ix.Name.fromLeanName target)
      | return (#["blob/record: the target is not published"], #[])
    let some lc := ixe₀.consts.get? named.addr
      | return (#["blob/record: the target's record is not stored"], #[])
    let bytes := lc.rawBytes
    let n := Nat.fromBytesLE bytes.data
    unless Nat.toBytesLE n == bytes.data do continue
    let literalC : Lean.ConstantInfo := .defnInfo
      { name := literal, levelParams := [], type := .const target (params.map fun _ => .zero),
        value := .lit (.natVal n),
        hints := .abbrev, safety := .safe, all := [literal] }
    let env ← IO.lazyPure fun _ =>
      Tests.Ix.Kernel.SourceIngressStep.canon #[(target, targetC), (literal, literalC)]
    match Ix.Cert.compileReport env with
    | .error e =>
      if (e.splitOn "blob check failed").length > 1 then
        return (#[], #[s!"blob/record: compileReport refuses a Nat literal whose bytes are another \
          constant's record ({bytes.size} bytes)"])
      return (#[s!"blob/record: the literal is refused, but not by the blob check: {e}"], #[])
    | .ok _ => return (#["blob/record: compileReport accepts a Nat literal whose bytes are another \
        constant's record"], #[])
  return (#["blob/record: every candidate target's record ends with a zero byte"], #[])

/-- **A recursor in another family's motive slot is refused** by `compileReport`'s
recursor check: `PUnit.rec` given `Bool.rec`'s type, rules and levels, with
`all = [PUnit]`, beside `Bool` and `PUnit` and without `Bool.rec`. The recursor
index attaches it to `Bool`'s block, whose motive its type eliminates, and no
recursor of `Bool`'s family is published there. -/
def recursorFamilyCase (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let mut consts : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for n in [``Bool, ``Bool.false, ``Bool.true, ``PUnit, ``PUnit.unit] do
    let some ci := leanEnv.find? n
      | return (#[s!"recursor family: {n} is not in the test environment"], #[])
    consts := consts.push (n, ci)
  let some (.recInfo rv) := leanEnv.find? ``Bool.rec
    | return (#["recursor family: Bool.rec is not a recursor of the test environment"], #[])
  let planted : Lean.Name := ``PUnit.rec
  consts := consts.push (planted, .recInfo { rv with name := planted, all := [``PUnit] })
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon consts
  match Ix.Cert.compileReport env with
  | .error e =>
    if (e.splitOn "recursor check failed").length > 1 then
      return (#[], #[s!"recursor family: compileReport refuses a recursor with all = [PUnit] in \
        Bool's motive slot: {e}"])
    return (#[s!"recursor family: the recursor is refused, but not by the recursor check: {e}"], #[])
  | .ok _ => return (#["recursor family: compileReport accepts a recursor with all = [PUnit] in \
      Bool's motive slot"], #[])

/-- **A record of the wrong kind at a bound role's address is refused** by
`compileReport`'s role check: the closure of `propext` and `Nat.add` compiles to
records at the addresses the default role table binds, and each such record of a
`Nat` operation or axiom role, read as a record of the other kind (a decoded
record that disagrees with its bytes, which the authenticity check does not
read), is refused. -/
def roleKindCase (leanEnv : Lean.Environment) : IO (Array String × Array String) := do
  let t ← match Ix.Kernel.Reader.defaultTable with
    | .ok t => pure t
    | .error e => return (#[s!"role kinds: the default role table failed: {e}"], #[])
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure leanEnv #[``propext, ``Nat.add])
  let env ← IO.lazyPure fun _ => Tests.Ix.Kernel.SourceIngressStep.canon closed.toArray 2
  let (ixe, failures, cenv) ← match Ix.Cert.compileUnchecked env with
    | .ok out => pure out
    | .error e => return (#[s!"role kinds: the closure failed to compile: {e}"], #[])
  if let .error e := Ix.Cert.checkReport env cenv (ixe, failures) then
    return (#[s!"role kinds: checkReport refuses the closure's own result: {e}"], #[])
  let mut errors : Array String := #[]
  let mut refused : Array String := #[]
  for (r, p) in t.bound do
    let some lc := ixe.consts.get? p | continue
    let some c := lc.get? | continue
    let other : Option Ixon.ConstantInfo :=
      match (Ix.Kernel.Role.spec (md := .anon) r).kind, c.info with
      | .ops, .defn d => some (.axio { isUnsafe := false, lvls := d.lvls, typ := d.typ })
      | .axiom, .axio ax =>
        some (.defn { kind := .defn, safety := .safe, lvls := ax.lvls, typ := ax.typ, value := ax.typ })
      | _, _ => none
    let some info := other | continue
    let ixe' : Ixon.Env := { ixe with consts := ixe.consts.insert p { lc with cache := some { c with info } } }
    match Ix.Cert.checkReport env cenv (ixe', failures) with
    | .error e =>
      if (e.splitOn "role check failed").length > 1 then refused := refused.push s!"{repr r}"
      else errors := errors.push s!"role kinds: the record of the wrong kind at {repr r}'s address is \
        refused, but not by the role check: {e}"
    | .ok () => errors := errors.push s!"role kinds: checkReport accepts a record of the wrong kind at \
        {repr r}'s address"
  if refused.isEmpty && errors.isEmpty then
    errors := errors.push "role kinds: the closure's artifact stores no record at a bound Nat \
      operation's or axiom role's address"
  if errors.isEmpty then
    return (#[], #[s!"role kinds: checkReport refuses a record of the wrong kind at the bound \
      address of {refused.toList}"])
  return (errors, #[])

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
  report "an axiom α-equal to sorryAx is published at its address and keyed by its role" (do
    sorryAliasCase (← getCompileEnv #[defsModule, ownModule])) 1,
  report "the statements' hypotheses and conclusion, per root, on the accepted fixtures" (do
    perRoot (← getCompileEnv #[defsModule, ownModule])) 1,
  report "binder contracts on both sides, on the resolved source-contract syntax fixtures" (do
    contractAgreement (← getCompileEnv #[syntaxModule])) 1,
  report "the shipped role table's certificates check on their pinned closure (Route A, B6b)"
    roleEvidenceCase 1,
  report "a closure with a well-founded Nat operation, at the bundle evidence (Nat.div)" (do
    natDivClosure (← getCompileEnv #[defsModule, ownModule])) 1,
  report "a closure with a string literal holds its literal support (outOfBounds)" (do
    literalClosure (← getCompileEnv #[defsModule, ownModule]) `outOfBounds) 1,
  report "a Nat literal whose bytes are another constant's record is refused (blob check)"
    blobRecordCase 1,
  report "a recursor with all = [J] in I's motive slot is refused (recursor check)" (do
    recursorFamilyCase (← getCompileEnv #[defsModule, ownModule])) 1,
  report "a record of the wrong kind at a bound role's address is refused (role check)" (do
    roleKindCase (← getCompileEnv #[defsModule, ownModule])) 1]

/-- `cert-evidence-agreement` (landing): the role table's evidence against quotient Source's on the
well-founded operations' closure (`evidenceAgreement`); it compiles and reads the closure, so it
stays out of the primary tier. -/
def evidenceSuite : List TestSeq := [
  report "the role table's evidence against quotient Source's, on the well-founded operations" (do
    evidenceAgreement (← getCompileEnv #[defsModule, ownModule])) 1]

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

/-- `cert-evidence-initstd`: the evidence check (part of the artifact checks) on the compiled
Init+Std, timed. -/
def evidenceInitStdSuite : List TestSeq := [
  report "the evidence check on the compiled Init+Std" (do
    let leanEnv ← getCompileEnv #[`Init, `Std]
    let dir ← IO.FS.createTempDir
    let ixe ← try
        let path := dir / "initstd.ixe"
        let _ ← Ix.CompileM.rsCompileEnvBytes leanEnv path.toString
        IO.ofExcept (Ixon.deEnv (← IO.FS.readBinFile path))
      finally IO.FS.removeDirAll dir
    let some t := defaultTable? | return (#["evidence: the default role table does not read"], #[])
    let started ← IO.monoMsNow
    let checked ← IO.lazyPure fun _ => Ix.Cert.EvidenceCheck.evidenceCheck t ixe
    let ms := (← IO.monoMsNow) - started
    match checked with
    | .ok () => return (#[], #[s!"evidence check on Init+Std ({ixe.consts.size} records): passes in {ms} ms"])
    | .error e => return (#[s!"evidence check on Init+Std refuses the artifact after {ms} ms: {e}"], #[])) 1]

/-- `cert-noctor-initstd` (ignored): N-READS N4 (a)'s premise `NoCtorIn` on every inductive of
Init+Std. -/
def noCtorInitStdSuite : List TestSeq := [
  report "no constructor of a family in its types, on Init+Std (N-READS N4 a)" (do
    let leanEnv ← getCompileEnv #[`Init, `Std]
    let env ← IO.lazyPure fun _ =>
      Tests.Ix.Kernel.SourceIngressStep.canon leanEnv.constants.toList.toArray 16
    noCtorCases "Init+Std" env) 1]


end Tests.Ix.Cert.Statement
