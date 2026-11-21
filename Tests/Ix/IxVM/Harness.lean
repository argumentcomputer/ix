module

public import Ix.Cli.FormalAiur
public import Ix.IxVM.ClaimHarness
public import Ix.Aiur.Statistics
public import Ix.AiurInvocation
public import Ix.IxVM.RecordSections

/-!
# Running claims through the IxVM program

The IxVM suites submit claims to the formal IxVM program and pin each verdict.
A case is a claim witness built by `IxVM.ClaimHarness`, as `ix check` builds
one, with the verdict it must get and, for a rejection, text the error must
contain. The cases run in the production host, `ixvm-proof test`, against the
trusted claim artifact: the same program, entry point (`IxVM::verify_claim`)
and witness preparation as `ix check` and `ix prove`.

Three helpers name what the suites run against, so that a change in how the
program is produced (elaborated from Lean, serialized as Ixon) changes them
only:

- `programArtifact` is the IxVM claim artifact: `$IX_AIUR_ARTIFACT`, or the
  checkout's cached export (`lake build ix`), exported on first use;
- `programHost` is the Rust host: `$IX_AIUR_HOST`, or the checkout's
  `ixvm-proof`, rebuilt from the checkout's crates on each use;
- `programSources` is the program's source text, which the guards over its
  literals and IO reads scan.

`$IX_TEST_OUTPUT_DIR`, when set, keeps the case files, so that a failing case
can be rerun alone with `ixvm-proof test <artifact> <file>`. Cases with FFT
pins also request a `.stats.json` sidecar from the host with `--stats-out`.
Lean computes and checks the costs from those raw measurements.

## Circuit verdict

Ordinary execution skips the assertions the program exports with
`runtimeCheck := false` (`constrain_eq!`: the `u32`/`u64` gadgets' range and
recomposition checks, `KernelNatPrim`'s `split_u32`), which only the circuit
enforces. In circuit-verdict mode the host checks every assertion, so a case's
verdict is the circuit's on the case's witness. The circuit verdict is the
suites' verdict: the harness runs every case file in circuit-verdict mode
unless `$IX_AIUR_CIRCUIT_VERDICT=0` selects plain execution or a suite pins a
mode with `circuit`. The host acknowledges the mode in its output; a case file
whose host did not is a failure, so that a stale host cannot pass a suite in
the wrong mode.
-/

public section

namespace Tests.Ix.IxVM

open IxVM.ClaimHarness

/-- The IxVM claim artifact the suites execute: `$IX_AIUR_ARTIFACT`, or the
checkout's cached export. -/
def programArtifact : IO String := Ix.Cli.FormalAiur.artifactPath default

/-- The Rust host that executes the cases (`ixvm-proof test`):
`$IX_AIUR_HOST`, or the checkout's release build, built when missing. -/
def programHost : IO String := do
  if let some path ← IO.getEnv "IX_AIUR_HOST" then return path
  let root ← Ix.Cli.FormalAiur.repoRoot
  let path := root / "target" / "release" / "ixvm-proof"
  -- Cargo rebuilds only what changed, so a host built from older crates is
  -- never reused: its grouping and widths would decide verdicts and costs.
  Ix.Cli.FormalAiur.command "cargo" #["build", "--release", "--locked", "-p", "ixvm",
    "--bin", "ixvm-proof", "--features", "parallel"] root
  return path.toString

/-- The Aiur source text of a program's modules as `(file, text)`, in file-name
order: the body of the `aiur⟦ … ⟧` block of each `.lean` file in `dir`, by
default the IxVM program's modules, without `--` comment lines. Named DSL
modules retain all function quotations; legacy module quotations (used by
MultiStark) retain their whole block. Missing declarations fail the guard. -/
def programSources (dir : System.FilePath := "IxVM/IxVM/Source") :
    IO (Array (System.FilePath × String)) := do
  let dir := (← Ix.Cli.FormalAiur.repoRoot) / dir
  let files := ((← dir.readDir).map (·.path)).filter (·.extension == some "lean")
  let mut out := #[]
  for file in files.qsort (·.toString < ·.toString) do
    let text ← IO.FS.readFile file
    let lines := text.splitOn "\n"
    let named := lines.dropWhile fun l => !l.trimAscii.toString.startsWith "aiur_module "
    let lines ← if !named.isEmpty then pure named else do
      let (head :: _ :: _) := text.splitOn "\n⟧"
        | throw (IO.userError s!"{file} has no Aiur declarations")
      let parts := head.splitOn "aiur⟦"
      unless parts.length ≥ 2 do throw (IO.userError s!"{file} has no Aiur declarations")
      pure ((parts.getLastD "").splitOn "\n")
    out := out.push (file, "\n".intercalate (lines.filter
      fun l => !l.trimAscii.toString.startsWith "--"))
  if out.isEmpty then throw (IO.userError s!"{dir} holds no module files")
  return out

/-- A claim submitted to the IxVM program, with its expected verdict. -/
structure Case where
  label : String
  /-- Whether the program must accept the claim. -/
  accept : Bool
  /-- For a rejection: text the execution error must contain, such as the
  failing assertion's message. Without it, any failure of the program counts,
  except a witness that lacks data the program asks for (`missing hint`). -/
  rejectsWith : Option String := none
  /-- For an acceptance: a function of the program the execution must call,
  such as the native rule a case targets. -/
  exercises : Option String := none
  /-- Exact rounded FFT-work surrogate of the accepted execution. -/
  expectedFftCost : Option Nat := none
  /-- Upper-bound rounded FFT-work budget of the accepted execution. -/
  maxFftCost : Option Nat := none
  witness : ClaimWitness

/-! ## Binder data for hand-built records

Records the compiler writes carry their binder-data section. The suites also
build records by hand, without one, and name them in claims, trees and role
tables by the address of their bytes. `withRecordSections` gives each decodable
record that has no section but has a binder its section from IxC's pass
(`IxVM.RecordSections`; `never` where the pass cannot compute a datum, so a
deliberately ill-typed record is still rejected where it was), re-addresses it and
every record that names it, and renames the environment's names, hints, role
binding, assumptions, the claim and its trees to follow. Every other record keeps
its bytes (as does a record whose bytes are not its canonical encoding), so a hand-crafted
encoding stays as it was. A re-addressed record's old version is dropped, as the
compiler would never have written it, unless a hand-crafted record still names it: left
in, an old axiom that the renamed role table no longer binds would become one of the
environment's user axioms (`Ix.ClaimContext.userAxioms`), without its section. -/

/-- Whether `c` lacks the section it needs: none, and a binder in a root. -/
def needsSection (c : Ixon.Constant) : Bool :=
  c.binders.isEmpty &&
    (_root_.IxVM.PwHints.roots c).any (_root_.IxVM.PwHints.hasBinder (_root_.IxVM.PwHints.binderful c.sharing))

/-- A claim context with its binding renamed by `a` and its axioms tree by `t`. -/
def renameCtx (a t : Address → Address) (ctx : Ix.ClaimContext) : Ix.ClaimContext :=
  { ctx with binding := a ctx.binding, axioms := ctx.axioms.map t }

/-- `claim` with its addresses renamed: constants by `a`, tree roots by `t`. -/
def renameClaim (a t : Address → Address) : Ix.Claim → Ix.Claim
  | .eval ctx i o asm => .eval (renameCtx a t ctx) (a i) (a o) (asm.map t)
  | .check ctx c asm => .check (renameCtx a t ctx) (a c) (asm.map t)
  | .checkEnv ctx r asm => .checkEnv (renameCtx a t ctx) (t r) (asm.map t)
  | .reveal c info binders => .reveal (a c) (match info with
    | .cPrj i k b => .cPrj i k (b.map a)
    | .rPrj i b => .rPrj i (b.map a)
    | .iPrj i b => .iPrj i (b.map a)
    | .dPrj i b => .dPrj i (b.map a)
    | other => other) binders
  | .contains tree c => .contains (t tree) (a c)
  | .catalog members => .catalog (t members)
  | .binding spec b => .binding spec (a b)
  | .compile cc => .compile { cc with env := t cc.env, roleTable := cc.roleTable.map a, target := a cc.target }

/-- Whether a `LazyConstant` may lack its binder-data section (`c.binders.isEmpty`).
A canonical Ixon v5 constant with an empty binder section ends with the byte `0x00`
(`numBinders = 0`). When `cache` is populated we check `needsSection c` directly; when
`cache` is `none` (an unparsed slice), a non-zero trailing byte guarantees `c.binders`
is non-empty (or the bytes are non-canonical), avoiding deserialization altogether. -/
private def mayNeedSection (lc : Ixon.LazyConstant) : Bool :=
  match lc.cache with
  | some c => needsSection c
  | none => lc.len > 0 && lc.off + lc.len ≤ lc.buf.size && lc.buf[lc.off + lc.len - 1]! == 0

/-- `env`, `claim` and `trees` with every hand-built record that needs one given
its section. Nothing changes when no record needs one. -/
def withRecordSections (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree) :
    Except String (Ixon.Env × Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  -- Pass 1: find canonical records that actually need a binder-data section.
  -- Check `mayNeedSection` / `needsSection` before calling `serConstant`, so compiled
  -- environments return immediately without deserializing or re-serializing `env.consts`.
  let mut pending : Array (Address × Ixon.Constant) := #[]
  let mut pendingSet : Std.HashSet Address := {}
  for (a, lc) in env.consts do
    if !mayNeedSection lc then continue
    if let some c := lc.get? then
      if needsSection c && Ixon.serConstant c == lc.rawBytes then
        pending := pending.push (a, c)
        pendingSet := pendingSet.insert a
  if pending.isEmpty then return (env, claim, trees)
  -- Build `support` from only the transitive dependency closure of `pending` (plus any
  -- recursor records in `env.consts` for inductive blocks reached by that closure, so IxC
  -- installs those blocks with their recursors instead of passing all of `env.consts`).
  let drain (closed : Std.HashMap Address Ixon.Constant) (worklist : Array Address) :
      Std.HashMap Address Ixon.Constant := Id.run do
    let mut closed := closed
    let mut wl := worklist
    while !wl.isEmpty do
      let a := wl.back!
      wl := wl.pop
      if closed.contains a then continue
      let some lc := env.consts[a]? | continue
      let some c := lc.get? | continue
      if Ixon.serConstant c != lc.rawBytes then continue
      closed := closed.insert a c
      for r in closureEdgesOf a c do
        if !closed.contains r then wl := wl.push r
    return closed
  let mut closed : Std.HashMap Address Ixon.Constant := {}
  let mut initialSeeds : Array Address := #[]
  for (a, c) in pending do
    closed := closed.insert a c
    for r in closureEdgesOf a c do
      initialSeeds := initialSeeds.push r
  closed := drain closed initialSeeds
  let mut addedRecs := true
  while addedRecs do
    addedRecs := false
    let mut indBlocks : Std.HashSet Address := {}
    for (a, c) in closed do
      if let .muts ms := c.info then
        if ms.any (fun | .indc _ => true | _ => false) then
          indBlocks := indBlocks.insert a
    if indBlocks.isEmpty then break
    let mut recSeeds : Array Address := #[]
    for (a, lc) in env.consts do
      if closed.contains a then continue
      let isRecCandidate := match lc.cache with
        | some c => match c.info with
          | .recr _ => true
          | .muts ms => ms.any (fun | .recr _ => true | _ => false)
          | _ => false
        | none => match lc.peekTag with
          | .ok .recr | .ok .muts => true
          | _ => false
      if !isRecCandidate then continue
      let some c := lc.get? | continue
      let isRec := match c.info with
        | .recr _ => true
        | .muts ms => ms.any (fun | .recr _ => true | _ => false)
        | _ => false
      if !isRec then continue
      let pointsToInd := c.refs.any fun r =>
        indBlocks.contains r ||
        match env.getConst? r with
        | some rc => match rc.info with
          | .iPrj p => indBlocks.contains p.block
          | _ => false
        | none => false
      if pointsToInd then
        recSeeds := recSeeds.push a
    if !recSeeds.isEmpty then
      closed := drain closed recSeeds
      addedRecs := true
  let mut support : Array (Address × Ixon.Constant) := #[]
  for (a, c) in closed do
    unless pendingSet.contains a do
      support := support.push (a, c)
  let sections ← _root_.IxVM.RecordSections.sectionsOf pending support env.blobs env.anonHints
    (← _root_.IxVM.RecordSections.chosenOf env) (taint := false)
  -- The records to rewrite: those needing a section, and every canonical record
  -- transitively naming one. Non-canonical records naming one keep its old address alive.
  let mut affected : Std.HashSet Address := pendingSet
  let mut affectedStore : Std.HashMap Address Ixon.Constant :=
    pending.foldl (fun m (a, c) => m.insert a c) {}
  let mut stillNamed : Std.HashSet Address := {}
  let mut nonCanonical : Std.HashSet Address := {}
  let mut grown := true
  while grown do
    grown := false
    for (a, lc) in env.consts do
      if affected.contains a || nonCanonical.contains a then continue
      match lc.get? with
      | none =>
        nonCanonical := nonCanonical.insert a
      | some c =>
        if (Ix.Compile.BinderData.targets c).any affected.contains then
          if Ixon.serConstant c == lc.rawBytes then
            affected := affected.insert a
            affectedStore := affectedStore.insert a c
            grown := true
          else
            nonCanonical := nonCanonical.insert a
            for x in Ix.Compile.BinderData.targets c do stillNamed := stillNamed.insert x
  let order ← Ix.Compile.BinderData.bottomUp affectedStore affectedStore.toArray
  let mut renamed : Std.HashMap Address Address := {}
  let mut consts := env.consts
  for a in order do
    unless affected.contains a do continue
    let some c := affectedStore[a]? | continue
    let rename (x : Address) : Address := renamed.getD x x
    let binders := if pendingSet.contains a then sections.getD a #[] else c.binders
    let c' := Ix.Compile.BinderData.rewriteRecord rename c binders
    let bytes := Ixon.serConstant c'
    let a' := Address.blake3 bytes
    consts := consts.insert a' { buf := bytes, len := bytes.size, cache := some c' }
    renamed := renamed.insert a a'
  for (a, a') in renamed do
    unless a == a' || stillNamed.contains a do consts := consts.erase a
  let rename (x : Address) : Address := renamed.getD x x
  let named := env.named.fold (init := ({} : Std.HashMap Ix.Name Ixon.Named)) fun m n entry =>
    m.insert n { entry with addr := rename entry.addr
                            original := entry.original.map fun (x, cm) => (rename x, cm) }
  let addrToName := env.addrToName.fold (init := ({} : Std.HashMap Address Ix.Name)) fun m x n =>
    m.insert (rename x) n
  let anonHints := env.anonHints.fold
    (init := ({} : Std.HashMap Address Lean.ReducibilityHints)) fun m x h => m.insert (rename x) h
  let mut addrMap := renamed
  let roleBinding ← match env.roleBinding with
    | none => pure none
    | some b => do
      let some t := Ix.Kernel.RoleTable.ofBytes b.bytes | pure (some b)
      let bytes := (Ix.Compile.BinderData.renameTable rename t).toBytes
      if bytes == b.bytes then pure (some b) else pure (some { address := Address.blake3 bytes, bytes })
  if let (some b, some b') := (env.roleBinding, roleBinding) then
    unless b.address == b'.address do addrMap := addrMap.insert b.address b'.address
  let env' := { env with
    consts, named, addrToName, anonHints, roleBinding
    main := env.main.map rename
    assumptions := env.assumptions.fold (init := ({} : Std.HashSet Address)) fun s x => s.insert (rename x) }
  -- the trees: a tree with a renamed leaf is rebuilt canonically
  let mut treeMap : Std.HashMap Address Address := {}
  let mut trees' : Std.HashMap Address Ix.AssumptionTree := {}
  for (root, tree) in trees do
    let leaves := tree.leaves
    let leaves' := leaves.map rename
    if leaves' == leaves then trees' := trees'.insert root tree
    else match Ix.AssumptionTree.canonical leaves' with
      | some t =>
        trees' := trees'.insert t.root t
        treeMap := treeMap.insert root t.root
      | none => trees' := trees'.insert root tree
  if let (some old, some new) := (Ix.ClaimContext.userAxiomTree env, Ix.ClaimContext.userAxiomTree env') then
    unless old.root == new.root do treeMap := treeMap.insert old.root new.root
  let a (x : Address) : Address := addrMap.getD x x
  let t (x : Address) : Address := treeMap.getD x x
  return (env', renameClaim a t claim, trees')

/-- `c` with the section of its safe twin (each unsafe or partial definition made safe),
typed against `env`. The compiler leaves every binder of an unsafe or partial record
undecided, which IxVM refuses when it reads it; data are untrusted, so a prover may attach
decided ones instead, and a case about IxVM's safety checks needs them to reach those
checks. -/
def withSafeTwinSection (env : Ixon.Env) (c : Ixon.Constant) : Except String Ixon.Constant := do
  let safe (d : Ixon.Definition) : Ixon.Definition := { d with safety := .safe }
  let info : Ixon.ConstantInfo := match c.info with
    | .defn d => .defn (safe d)
    | .muts ms => .muts (ms.map fun m => match m with
      | .defn d => .defn (safe d)
      | m => m)
    | i => i
  let twin ← _root_.IxVM.RecordSections.withSection env { c with info }
  return { c with binders := twin.binders }

/-- `buildClaimWitness` after `withRecordSections`. -/
def buildSectionedWitness (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {}) : Except String ClaimWitness := do
  let (env, claim, trees) ← withRecordSections env claim trees
  buildClaimWitness env claim trees

/-- The case for `claim` over `env`, with the assumption trees its roots name. -/
def Case.ofClaim (label : String) (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {}) (accept : Bool := true)
    (rejectsWith : Option String := none) : Except String Case := do
  let witness ← buildSectionedWitness env claim trees
  return { label, accept, rejectsWith, witness }

/-- Whether the program refuses every recursor of a mutual or nested family. It does not: the
refusal is removed from `KernelCheck::check_const`, and the family check runs at such a
recursor. A suite that claims such a recursor, or a constant whose closure holds one, expected
the refusal while it was in force. -/
def modeledRecursorsRefused : Bool := false

/-- The refusal's message. -/
def modeledRecursorRefusal : String := "a recursor of a mutual or nested family is refused"

/-- Retained compatibility identity helper for suites outside this batch (`ModelAdvice`,
`IndVariations`); recursors of mutual and nested families are no longer refused. -/
def Case.throughModeledRecursor (c : Case) : Case := c

/-! ## The case file

`ixvm-proof test` reads a case file in Ixon (`Ix.AiurInvocation`): a header,
the cases one at a time, each a label, the verdict, `rejects_with`,
`exercises` and the invocation (`Ix.Cli.FormalAiur.invocation`), and a
trailer. Witnesses carry megabytes of constant bytes, so a case is encoded
when it is written and then dropped. -/

/-- One case as it follows the header of a case file. -/
def Case.encode (c : Case) : ByteArray :=
  let invocation := Ix.Cli.FormalAiur.invocation c.witness.input c.witness.inputIOBuffer
  Ix.AiurInvocation.Case.encode
    { label := c.label, accept := c.accept, rejectsWith := c.rejectsWith,
      exercises := c.exercises, invocation := invocation }

/-- The stream elements of a case, the measure of its size. -/
def Case.size (c : Case) : Nat :=
  c.witness.inputIOBuffer.map.fold (init := c.witness.input.size) fun n _ info => n + info.len

/-! ## Running

A suite adds its cases to a `Runner` one at a time. A witness holds megabytes
of constant bytes, so each case is written to the current case file as it is
added and then dropped. A file of about `limit` stream elements, or of
`maxCases` cases, is closed and runs in a host process at once, up to `jobs`
at a time, while the suite builds the next cases. -/

/-- The case file being written: its path, handle, cases and stream elements.
Each entry in `fftPins` is `(label, cost, exact)`, where `exact = true` checks
`actual == cost` and `exact = false` checks `actual ≤ cost`. -/
structure OpenFile where
  path : System.FilePath
  handle : IO.FS.Handle
  cases : Nat
  size : Nat
  fftPins : Array (String × Nat × Bool) := #[]

structure Runner where
  suite : String
  dir : System.FilePath
  artifact : String
  host : String
  /-- Circuit-verdict mode: the host checks every assertion. -/
  circuit : Bool := false
  jobs : Nat
  limit : Nat
  maxCases : Nat
  current : IO.Ref (Option OpenFile)
  tasks : IO.Ref (Array (System.FilePath × Array (String × Nat × Bool) × Task (Except IO.Error IO.Process.Output)))
  labels : IO.Ref (Std.HashSet String)
  broken : IO.Ref Nat

/-- The host's switch for circuit-verdict mode. -/
def circuitVerdictVar : String := "IX_AIUR_CIRCUIT_VERDICT"

/-- The number of assertions the host says it enabled for circuit-verdict
mode, from its acknowledgement line. -/
def circuitAcknowledgement (stdout : String) : Option Nat :=
  (stdout.splitOn "\n").findSome? fun line =>
    match line.trimAscii.toString.splitOn " " with
    | "circuit" :: "verdict:" :: n :: _ => n.toNat?
    | _ => none

/-- Close the current file and run it. -/
private def Runner.flush (r : Runner) : IO Unit := do
  let some file ← r.current.get | return
  r.current.set none
  file.handle.write Ix.AiurInvocation.casesTrailer
  file.handle.flush
  let mut args := #["test", r.artifact, file.path.toString]
  unless file.fftPins.isEmpty do
    args := args ++ #["--stats-out", (file.path.withExtension "stats.json").toString]
  let tasks ← r.tasks.get
  if tasks.size ≥ r.jobs then
    let _ ← IO.wait tasks[tasks.size - r.jobs]!.2.2
  let env := #[(circuitVerdictVar, if r.circuit then some "1" else none)]
  let task ← IO.asTask (prio := .dedicated)
    (IO.Process.output { cmd := r.host, args, env })
  r.tasks.modify (·.push (file.path, file.fftPins, task))

/-- A case that could not be built: reported, and fails the suite. -/
def Runner.fail (r : Runner) (message : String) : IO Unit := do
  r.broken.modify (· + 1)
  IO.eprintln s!"[{r.suite}] {message}"

/-- Write `c` to the current case file. -/
def Runner.add (r : Runner) (c : Case) : IO Unit := do
  if (c.expectedFftCost.isSome || c.maxFftCost.isSome) && !c.accept then
    return ← r.fail s!"FFT pin on rejection case {c.label}"
  if (← r.labels.get).contains c.label then
    return ← r.fail s!"two cases are labelled {c.label}"
  r.labels.modify (·.insert c.label)
  let file ← match ← r.current.get with
    | some file => pure file
    | none => do
      let path := r.dir / s!"{r.suite}-{(← r.tasks.get).size}.ixt"
      let handle ← IO.FS.Handle.mk path .write
      handle.write Ix.AiurInvocation.casesHeader
      pure { path, handle, cases := 0, size := 0 }
  file.handle.write c.encode
  let fftPins := match c.expectedFftCost with
    | some cost => file.fftPins.push (c.label, cost, true)
    | none => file.fftPins
  let fftPins := match c.maxFftCost with
    | some budget => fftPins.push (c.label, budget, false)
    | none => fftPins
  let file := { file with cases := file.cases + 1, size := file.size + c.size, fftPins }
  r.current.set (some file)
  if file.size ≥ r.limit || file.cases ≥ r.maxCases then r.flush

/-- Build `c` and write it, or report why it could not be built. -/
def Runner.build (r : Runner) (c : Except String Case) : IO Unit :=
  match c with
  | .ok c => r.add c
  | .error e => r.fail s!"a case could not be built: {e}"

/-- Run the cases `body` adds through the IxVM program (`ixvm-proof test`).
Every case runs; the result is `0` when every case was built and every verdict
and FFT cost are the expected ones. The host reports verdicts and execution
times; Lean computes and checks costs from the raw statistics.
`ixvm-proof test` parallelizes cases internally with rayon, so default chunking
keeps medium suites in one `.ixt` batch (loading `ixvm.ixa` once) while bounding
peak memory for giant suites. -/
def withRunner (suite : String) (body : Runner → IO Unit) (jobs : Nat := 2)
    (limit : Nat := 64_000_000) (maxCases : Nat := 10_000) (circuit : Option Bool := none) :
    IO UInt32 := do
  let artifact ← programArtifact
  let host ← programHost
  -- The circuit verdict unless the environment asks for plain execution.
  let circuit ← match circuit with
    | some c => pure c
    | none => do pure ((← IO.getEnv circuitVerdictVar) != some "0")
  let go (dir : System.FilePath) : IO UInt32 := do
    IO.FS.createDirAll dir
    let started ← IO.monoMsNow
    let current ← IO.mkRef none
    let tasks ← IO.mkRef #[]
    let labels ← IO.mkRef {}
    let broken ← IO.mkRef 0
    let r : Runner := {
      suite := suite, dir := dir, artifact := artifact, host := host, circuit := circuit,
      jobs := jobs, limit := limit, maxCases := maxCases, current := current, tasks := tasks,
      labels := labels, broken := broken }
    try body r catch e => r.fail s!"building the cases failed: {e}"
    r.flush
    let mut failed := 0
    for (path, pins, task) in ← r.tasks.get do
      let out ← IO.ofExcept (← IO.wait task)
      IO.print out.stdout
      unless out.exitCode == 0 do
        failed := failed + 1
        IO.eprintln s!"[{suite}] {path}: {out.stderr.trimAscii}"
      if circuit then
        match circuitAcknowledgement out.stdout with
        | some 0 =>
          failed := failed + 1
          IO.eprintln s!"[{suite}] {path}: the host enabled no deferred assertion"
        | some _ => pure ()
        | none =>
          failed := failed + 1
          IO.eprintln s!"[{suite}] {path}: the host did not acknowledge circuit-verdict mode"
      unless pins.isEmpty do
        try
          let raw ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (path.withExtension "stats.json")))
          for (label, expected, exact) in pins do
            let measurements ← IO.ofExcept (raw.getObjVal? label >>= Aiur.ExecutionMeasurements.fromJson)
            let actual := (Aiur.computeStats measurements).roundedFftCost
            if exact then
              IO.println s!"FFT {label}: {actual} (expected {expected})"
              unless actual == expected do
                failed := failed + 1
                IO.eprintln s!"FAILED {label}: FFT cost {actual}, expected {expected}"
            else
              IO.println s!"FFT {label}: {actual} (budget ≤ {expected})"
              unless actual ≤ expected do
                failed := failed + 1
                IO.eprintln s!"FAILED {label}: FFT cost {actual} exceeds budget {expected}"
        catch e =>
          failed := failed + 1
          IO.eprintln s!"[{suite}] {path}: invalid or missing FFT statistics: {e}"
    let broken ← r.broken.get
    let mode := if circuit then "circuit verdict" else "execution verdict"
    IO.println s!"[{suite}] {(← r.labels.get).size} claims in {(← r.tasks.get).size} files \
      ({mode}), {(← IO.monoMsNow) - started} ms; {broken} cases not built, \
      {failed} verdict, statistics or FFT-pin failures"
    return if failed == 0 && broken == 0 then 0 else 1
  match ← IO.getEnv "IX_TEST_OUTPUT_DIR" with
  | some dir => go (System.FilePath.mk dir / "ixvm")
  | none => IO.FS.withTempDir go

/-- A case, built when it is written. -/
abbrev Builder := Unit → Except String Case

/-- Run `cases`, building them concurrently via bounded `IO.asTask` and writing each
in deterministic order so witnesses are dropped as they are flushed. -/
def runCases (suite : String) (cases : Array Builder) (jobs : Nat := 2)
    (circuit : Option Bool := none) : IO UInt32 :=
  withRunner suite (jobs := jobs) (circuit := circuit) fun r => do
    IO.println s!"[{suite}] {cases.size} claims through the IxVM program"
    let trace := (← IO.getEnv "IX_CASE_TRACE").isSome
    let buildOne (i : Nat) (build : Builder) : IO (Except String Case) := do
      if trace then IO.eprintln s!"[{suite}] building case {i}"
      let t0 ← IO.monoMsNow
      let c ← IO.lazyPure fun _ => build ()
      if trace then
        let label := match c with | .ok c => c.label | .error e => s!"(not built: {e})"
        IO.eprintln s!"[{suite}] built case {i} in {(← IO.monoMsNow) - t0} ms: {label}"
      return c
    let buildJobs := if trace then 1 else max 1 (min 16 cases.size)
    if buildJobs ≤ 1 then
      for (build, i) in cases.zipIdx do
        r.build (← buildOne i build)
    else
      let mut active : Array (Option (Task (Except IO.Error (Except String Case)))) :=
        Array.replicate buildJobs none
      try
        for i in [:buildJobs] do
          let b := cases[i]!
          active := active.set! i (some (← IO.asTask (prio := .dedicated) (buildOne i b)))
        let mut next := buildJobs
        for i in [:cases.size] do
          let slot := i % buildJobs
          let some task := active[slot]! | continue
          active := active.set! slot none
          let c ← IO.ofExcept (← IO.wait task)
          if next < cases.size then
            let idx := next
            let b := cases[idx]!
            active := active.set! slot (some (← IO.asTask (prio := .dedicated) (buildOne idx b)))
            next := next + 1
          r.build c
      finally
        for t? in active do
          if let some t := t? then
            discard (IO.wait t)

end Tests.Ix.IxVM

end
