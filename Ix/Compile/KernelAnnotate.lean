module

public import Ix.LeanIngress
public import Ix.KernelCheck.Step
public import Ix.Compile.BinderData
public import Ix.Compile.Parallel
public import Ix.Compile.FrontEnd
public import Ix.CompileM

public section

/-!
# The compiler's binder-data annotator: IxC's pass over the Lean source

`ix compile` writes every block record's binder-data section while it builds
the record, before the record is hashed (`Ix.CompileM.withBinderSection`). This
module is the annotator it runs there. The data are IxC's: its annotation pass
(`annotateBodyI`, its telescope loops `annotatePisI`/`annotateLamsI`) writes at
every binder the zero-ness of the codomain sort, by `annotPwPiI`/`annotPwLamI`
on the annotated opened body; nothing here infers anything itself.

**The environment.** Before the compile, IxC ingests the compile's own input
in Source mode (`Ix.LeanIngress`: every constant keyed by its Lean name, or its
role's key) and installs it with phase A of its fold
(`annotDeclStepWithUserAxioms`, at the committed bundle's evidence), once, in
dependency order (`install`). Unsafe and partial groups go through the typing
tier; a declaration that fails is retried after them, and one refused again
(a compiler-trust axiom, say) enters without its checks, with its
annotated type (`lenient`). The installed
environment and IxC's core over it are marked persistent: every worker reads
them, none writes them.

**The walk.** For a block record, each root is walked beside its member's
Source term (the Lean source converted as the ingress converts it): the
record's tree gives the numbering (its `lam`, `all` and `share` nodes in
pre-order, a share's entry a block of its own, one variant per distinct node
list), the Source term gives the leaves, and a datum's parameters are written
in the record's numbering (a large eliminator's source numbers its motive
universe last, its record first). The walk is IxC's pass over the pair:
a run of binders of one kind is opened in bulk, its leaf annotated, the datum
computed once at the leaf (every binder of the run has it, since the
zero-ness of `imax u v` is that of `v`) and the run closed with one
`abstractRangeC`; a `let` is ζ-reduced, its type and value annotated first; a
share is walked once per context of the variables it can name. Each record's
caches start empty and are dropped with it.

Where phase A annotated a root and stored it (a definition's type and value, a
theorem's, an opaque's or an axiom's type), the root's data are read off the
stored term beside the record's tree (`walkStored`), and nothing is inferred
again. A theorem's or an opaque's value, a block's or a quotient's roots, and a
root whose stored term and record differ are walked.

**Unsafe and partial records** carry the undecided section
(`Ix.CompileM.undecidedSection`). So does a record whose sources the annotator
cannot find or align, and every binder whose datum IxC's function cannot
compute, or under which something is undecided, is the undecided node.

The annotator is a pure function of its input (the installed environment, the
record and its sources). It is not trusted: the compiler keeps its section only
in canonical form (`Ix.CompileM.sectionAdmissible`), and a checker validates
every datum it reads.
-/

namespace Ix.Compile.KernelAnnotate

open Ix.Kernel (FEnv PropWhen BinderMeta)
open Ix.Kernel.Reader (CName CExpr CDecl ReadError State)
open Ix.LeanIngress
open IxVM.PwHints (Node Block)

abbrev KExpr := Ix.Kernel.Expr .source
abbrev CM := Ix.Kernel.Cached.CheckCM .source

/-! ## The installed environment -/

/-- IxC's environment of a compile's input, and what installing it found. -/
structure Installed where
  fe : FEnv .source
  core : Ix.Kernel.Cached.CoreFnsI .source
  /-- the compile's input, for the members' sources -/
  env : Ix.Environment
  installed : Nat := 0
  /-- the groups or declarations the ingress or the install refused, and why -/
  failures : Array (String × String) := #[]
  /-- the refused declarations entered without their checks (`lenient`) -/
  lenient : Nat := 0
  /-- the declarations phase A pushed from a wave's ahead-of-time annotation (`separable`) -/
  ahead : Nat := 0
  /-- phase A's waves -/
  waves : Nat := 0
  /-- the member names whose records are traced (`IX_BD_TRACE`, for diagnosis) -/
  trace : Array String := #[]
  /-- whether a root phase A annotated is read off its stored term (`walkStored`)
  rather than walked -/
  stored : Bool := true
  /-- the phases' times (ms) -/
  times : Array (String × Nat) := #[]

/-- The index of `env` (the newest constant of a key wins), by a loop. -/
def reindex (env : Ix.Kernel.Env .source) : FEnv .source := Id.run do
  let n := env.consts.length
  let mut idx : Std.HashMap (Ix.Kernel.Key .source) (Nat × Ix.Kernel.ConstantInfo .source) :=
    Std.HashMap.emptyWithCapacity n
  let mut i := n
  for ci in env.consts do
    i := i - 1
    unless idx.contains ci.name do idx := idx.insert ci.name (i, ci)
  return ⟨env, idx, n⟩

/-- One declaration through phase A of IxC's fold; on a failure, the environment
as it was. -/
def step (ev : Ix.Kernel.Evidences .source) (fe : FEnv .source) (pos : Nat)
    (d : Ix.Kernel.Declaration .source) :
    FEnv .source × Nat × Option (Ix.Kernel.CheckError .source) :=
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStepWithUserAxioms .verified ev (pos, fe, #[]) d {} with
  | .ok ((pos', fe', _), _) => (fe', pos', none)
  | .error (e, _) => (reindex before, pos + 1, some e)

/-- A declaration the kernel refuses, entered without its checks: its constant
with its annotated type (and a definition's annotated value, so that it
unfolds; a theorem keeps its value, which nothing reduces), as phase A would
have pushed it. The annotation is IxC's (`annotConstantValC`, `annotValueC`);
only the step's policy and checks are skipped. `none` where the annotation
itself fails. The data are not checked here: the annotator is not trusted. -/
def lenient (fe : FEnv .source) (d : Ix.Kernel.Declaration .source) : Option (FEnv .source) :=
  let run {α : Type} (act : CM α) : Option α := match act.run {} with
    | .ok (a, _) => some a
    | .error _ => none
  match d with
  | .axiomDecl cv =>
    (run (Ix.Kernel.Cached.annotConstantValC .verified fe cv)).map fun r => fe.push (.axiomInfo r.1)
  | .opaqueDecl cv _ =>
    (run (Ix.Kernel.Cached.annotConstantValC .verified fe cv)).map fun r => fe.push (.axiomInfo r.1)
  | .thmDecl cv v =>
    (run (Ix.Kernel.Cached.annotConstantValC .verified fe cv)).map fun r => fe.push (.thmInfo r.1 v)
  | .defnDecl cv v h =>
    (run (Ix.Kernel.Cached.annotValueC .verified fe cv v)).map fun r =>
      fe.push (.defnInfo r.1 r.2.2 h)
  | _ => none

/-- What phase A pushes for a separable declaration (a definition other than a
pinned `Nat` operation, a theorem, an opaque), computed against `fe`:
`annotStepC`'s install halves (`annotValueC`, `annotConstantValC`) from the
empty memo state, which every step starts from. `none` for any other
declaration, or where the annotation fails.

Phase A runs this ahead, on a wave of declarations at once, against the
environment before the wave, and pushes each result in order unless the
environment has meanwhile gained its name (the step's duplicate check). An
environment that holds more constants answers every lookup the annotation made
the same way, and a datum is unique, so the push is the step's. Any other
declaration is run ahead by `aheadStep`. -/
def separable (fe : FEnv .source) (d : CDecl .source) : Option (Ix.Kernel.ConstantInfo .source) :=
  let run {α : Type} (act : CM α) : Option α := match act.run {} with
    | .ok (a, _) => some a
    | .error _ => none
  if d.anchorMismatch?.isSome then none else
  match d with
  | .defnDecl cv v h =>
    if Ix.Kernel.natOpNames.contains cv.name || Ix.Kernel.natDivModNames.contains cv.name then none
    else (run (Ix.Kernel.Cached.annotValueC .verified fe cv v)).map fun r => .defnInfo r.1 r.2.2 h
  | .thmDecl cv v =>
    (run (Ix.Kernel.Cached.annotConstantValC .verified fe cv)).map fun r => .thmInfo r.1 v
  | .opaqueDecl cv v =>
    (run (Ix.Kernel.Cached.annotValueC .verified fe cv v)).map fun r => .axiomInfo r.1
  | _ => none

/-- What the ordinary step pushes for `d` against `fe`, in push order, for a
declaration that is not separable (a block, an axiom, a pinned `Nat`
operation...); `none` where the step fails. Run ahead on a wave like
`separable`, and pushed in order under the same duplicate check: the step
pushes the same constants against an environment that holds more. (The
step's first push copies `fe`'s index, which every task shares.) -/
def aheadStep (ev : Ix.Kernel.Evidences .source) (fe : FEnv .source) (d : CDecl .source) :
    Option (Array (Ix.Kernel.ConstantInfo .source)) :=
  match Ix.Kernel.Cached.annotDeclStepWithUserAxioms .verified ev (0, fe, #[]) d {} with
  | .ok ((_, fe', _), _) =>
    some (fe'.env.consts.take (fe'.visibleBelow - fe.visibleBelow)).reverse.toArray
  | .error _ => none

/-- A declaration's pushes computed ahead against `fe`: `separable`'s, else
`aheadStep`'s. -/
def ahead (ev : Ix.Kernel.Evidences .source) (fe : FEnv .source) (d : CDecl .source) :
    Option (Array (Ix.Kernel.ConstantInfo .source)) :=
  match d with
  | .defnDecl cv .. =>
    if Ix.Kernel.natOpNames.contains cv.name || Ix.Kernel.natDivModNames.contains cv.name then
      aheadStep ev fe d
    else (separable fe d).map (#[·])
  | .thmDecl .. | .opaqueDecl .. => (separable fe d).map (#[·])
  | _ => aheadStep ev fe d

/-- A kernel error on one line, for `IX_BD_TRACE`. -/
def traceError (e : Ix.Kernel.CheckError .source) : String :=
  ((Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2.replace "\n" " ").take 400

def readErrorString : ReadError → String
  | .malformed m => s!"malformed: {m}"
  | .declined m => s!"declined: {m}"

/-- The name a declaration is reported under. -/
def declName (d : Ix.Kernel.Declaration .source) : String :=
  match d.names.head? with
  | some k => toString k
  | none => "?"

private instance : Nonempty (FEnv .source) := ⟨Ix.Kernel.mkFEnv Ix.Kernel.Env.empty⟩

private instance : Nonempty (Ix.Kernel.Cached.CoreFnsI .source) :=
  ⟨Ix.Kernel.Cached.coreKnotI .verified (Ix.Kernel.mkFEnv Ix.Kernel.Env.empty) 0⟩

/-- `Ix.LeanIngress.graphOf`, with each group's literal kinds (`literalKinds`,
a walk of all its terms) computed on `width` tasks: the same graph. -/
def graphOfPar (width : Nat) (blocks : Ix.CondensedBlocks) (groups : Array Group)
    (converted : Array (Except ReadError Converted)) : Graph := Id.run do
  let supportNames := Ix.Kernel.Reader.strLitSupportNames
  let mut groupOf : Ix.Map TableName Nat := {}
  let mut supportOf : Std.HashMap (CName .source) Nat := {}
  for (g, i) in groups.zipIdx do
    for n in g.names do
      groupOf := groupOf.insert n i
      if let some k := supportNames.find? (nameIs n) then supportOf := supportOf.insert k i
  let mut hard : Array (Array Nat) := #[]
  let mut unplaced : Array (Option ReadError) := #[]
  for (g, i) in groups.zipIdx do
    let mut seenLo : Ix.Set TableName := {}
    let mut ds : Std.HashSet Nat := {}
    let mut bad : Option ReadError := none
    for n in g.names do
      let some lo := blocks.lowLinks.get? n
        | if bad.isNone then
            bad := some (.malformed s!"constant {ingressName n} is not in the condensation")
      if seenLo.contains lo then continue
      seenLo := seenLo.insert lo
      for r in (blocks.blockRefs.get? lo).getD {} do
        match groupOf.get? r with
        | some j => if j != i then ds := ds.insert j
        | none =>
          if bad.isNone then
            bad := some (.malformed s!"references {ingressName r}, which is not in the environment")
    hard := hard.push (ds.toArray.qsort (· < ·))
    unplaced := unplaced.push bad
  let support (names : List (CName .source)) : Array Nat :=
    names.foldl (fun acc n => match supportOf[n]? with
      | some j => if acc.contains j then acc else acc.push j
      | none => acc) #[]
  let natTargets := support Ix.Kernel.Reader.natLitSupportNames
  let strTargets := support supportNames
  let kinds := Ix.Compile.Parallel.map width (fun (c : Except ReadError Converted) => match c with
    | .ok c => some (literalKinds c)
    | .error _ => none) converted
  let literal := kinds.zipIdx.map fun (k, i) => match k with
    | some (nat, str) => (if str then strTargets else if nat then natTargets else #[]).filter (· != i)
    | none => #[]
  return ⟨groups, converted, hard, literal, unplaced⟩

/-- **Install the compile's input** in Source mode, phase A only, and mark the
environment and IxC's core over it persistent. -/
def install (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (workers : Nat := 32)
    (parallel : Bool := true) : IO (Except String Installed) := do
  let t0 ← IO.monoMsNow
  let pre ← match (Ix.Kernel.Reader.builtinPrelude : Except String (Ix.Kernel.Reader.Prelude .source)) with
    | .ok p => pure p
    | .error e => return .error s!"binder data: the prelude does not read: {e}"
  let tPre ← IO.monoMsNow
  let groups ← IO.lazyPure fun _ => groupsOf env blocks
  let tGroups ← IO.monoMsNow
  let converted ← IO.lazyPure fun _ => Ix.Compile.Parallel.map (4 * max workers 1) convert groups
  let tConv ← IO.monoMsNow
  let g ← IO.lazyPure fun _ => graphOfPar (4 * max workers 1) blocks groups converted
  let tGraph ← IO.monoMsNow
  let tierConv : Array (Option (Except ReadError (Ix.Kernel.Tier.TierDecl .source))) ←
    IO.lazyPure fun _ => groups.map fun grp => if isTierGroup grp then some (convertTier grp) else none
  let gT : Graph := { g with converted := g.converted.zipIdx.map fun (c, i) =>
    if (tierConv[i]!).isSome then .ok (.definitions #[]) else c }
  let sched ← IO.lazyPure fun _ => scheduleOf gT
  let t1 ← IO.monoMsNow
  let groupName (gi : Nat) : String := match (groups[gi]!.names)[0]? with
    | some n => n.pretty
    | none => "?"
  -- each group's depth in the reference graph (`sched` is in dependency order)
  let mut glevel : Array Nat := Array.replicate groups.size 0
  for (gi, _) in sched do
    let l := (gT.hard[gi]! ++ gT.literal[gi]!).foldl (fun m j => max m (glevel[j]! + 1)) 0
    glevel := glevel.set! gi l
  let mut st : State .source := pre.state
  let mut lowered : Array (CDecl .source) := #[]
  let mut levelOf : Std.HashMap (Ix.Kernel.Key .source) Nat := {}
  let mut tiers : Array (Nat × Ix.Kernel.Tier.TierDecl .source) := #[]
  let mut failures : Array (String × String) := #[]
  for (gi, c) in sched do
    if let some t := tierConv[gi]! then
      match t with
      | .ok d => tiers := tiers.push (gi, d)
      | .error e => failures := failures.push (groupName gi, readErrorString e)
      continue
    match c >>= fun c => lower st c with
    | .ok r =>
      st := st.commit r
      lowered := lowered ++ r.decls
      for d in r.decls do
        if let some k := d.names.head? then levelOf := levelOf.insert k glevel[gi]!
    | .error e => failures := failures.push (groupName gi, readErrorString e)
  let t2 ← IO.monoMsNow
  let canon ← IO.lazyPure fun _ => Ix.Compile.Parallel.map (4 * max workers 1) canonDecl lowered
  let tCanon ← IO.monoMsNow
  let prepared ← IO.lazyPure fun _ => Ix.Kernel.Frontend.preparePrelude pre.ix canon
  let tPrep ← IO.monoMsNow
  let ev ← IO.lazyPure fun _ => Ix.RoleEvidence.bundleEvidence ()
  let t3 ← IO.monoMsNow
  -- phase A in waves: the prelude's declarations first (wave 0), then each
  -- declaration at its group's depth plus one
  let front := pre.ix.decls.size
  let mut waves : Array (Array Nat) := #[]
  for h : i in [:prepared.size] do
    let l := if i < front then 0 else
      1 + ((prepared[i].names.head?.bind (levelOf[·]?)).getD 0)
    while waves.size ≤ l do waves := waves.push #[]
    waves := waves.modify l (·.push i)
  let mut fe : FEnv .source := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
  let mut pos := 0
  let mut ok := 0
  let mut ahead := 0
  let mut retry : Array (CDecl .source) := #[]
  -- phase A's time (ns): the waves' ahead-of-time annotation, the pushes of its
  -- results, the ordinary steps
  let mut nsAhead := 0
  let mut nsPush := 0
  let mut nsStep := 0
  for wave in waves do
    -- the wave's separable declarations, annotated against the environment as
    -- it stands before the wave (`separable`)
    let base := fe
    let n0 ← IO.monoNanosNow
    let pushes : Array (Option (Array (Ix.Kernel.ConstantInfo .source))) ← IO.lazyPure fun _ =>
      if !parallel || wave.size < 8 then wave.map fun _ => none
      else Ix.Compile.Parallel.map (4 * max workers 1) (fun i => ahead ev base prepared[i]!) wave
    let n1 ← IO.monoNanosNow
    nsAhead := nsAhead + (n1 - n0)
    for (i, r) in wave.zip pushes do
      if let some cis := r then
        if cis.all fun ci => (fe.find? ci.name).isNone then
          let m0 ← IO.monoNanosNow
          for ci in cis do
            let ci ← (unsafe Runtime.markPersistent ci : BaseIO (Ix.Kernel.ConstantInfo .source))
            fe := fe.push ci
          nsPush := nsPush + ((← IO.monoNanosNow) - m0)
          pos := pos + 1
          ok := ok + 1
          ahead := ahead + 1
          continue
      let d := prepared[i]!
      let m0 ← IO.monoNanosNow
      let (fe', pos', err) ← IO.lazyPure fun _ => step ev fe pos d
      nsStep := nsStep + ((← IO.monoNanosNow) - m0)
      fe := fe'
      pos := pos'
      match err with
      | none => ok := ok + 1
      | some _ => retry := retry.push d
  let t4 ← IO.monoMsNow
  -- the typing tier, then the declarations that failed before it (those that
  -- reference a tier constant)
  let logical := fe
  for (gi, d) in Benchmarks.Kernel.CheckIxeStep.stageDeferred (·.2) tiers do
    let (fe', err) := Benchmarks.Kernel.CheckIxeStep.stepTier logical fe d
    fe := fe'
    match err with
    | none => ok := ok + 1
    | some e =>
      let why := (Benchmarks.Kernel.CheckIxeStep.tierOutcome d.safety e).2
      failures := failures.push (groupName gi, why)
  -- a declaration refused again enters leniently (`lenient`), so that the
  -- records referencing it are annotated
  let mut lenientCount := 0
  for d in retry do
    let (fe', pos', err) := step ev fe pos d
    fe := fe'
    pos := pos'
    match err with
    | none => ok := ok + 1
    | some e =>
      let why := (Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2
      failures := failures.push (declName d, why)
      if let some fe' := lenient fe d then
        fe := fe'
        lenientCount := lenientCount + 1
  let t5 ← IO.monoMsNow
  let shared ← (unsafe Runtime.markPersistent fe : BaseIO (FEnv .source))
  let core ← (unsafe Runtime.markPersistent
    (Ix.Kernel.Cached.coreKnotI .verified shared Ix.Kernel.checkFuel) :
      BaseIO (Ix.Kernel.Cached.CoreFnsI .source))
  let t6 ← IO.monoMsNow
  return .ok { fe := shared, core, env, installed := ok, failures, lenient := lenientCount,
               ahead, waves := waves.size,
               times := #[("prelude", tPre - t0), ("groups", tGroups - tPre), ("convert", tConv - tGroups),
                 ("graph", tGraph - tConv), ("schedule", t1 - tGraph), ("lower", t2 - t1), ("canon", tCanon - t2), ("prepare", tPrep - tCanon), ("evidence", t3 - tPrep),
                 ("phaseA", t4 - t3), ("A:ahead", nsAhead / 1000000), ("A:push", nsPush / 1000000),
                 ("A:step", nsStep / 1000000), ("tier+retry", t5 - t4), ("persist", t6 - t5)] }

/-- **Install a compile's input**: its condensation (`Ix.CondenseM`, as the
compile's front end builds it), then `install`. For measurement (the data are
the same): with `IX_BD_SEQUENTIAL` set phase A takes every step in turn, with
`IX_BD_WALK_ALL` every root is walked. -/
def installInput (env : Ix.Environment) (workers : Nat := 32) : IO (Except String Installed) := do
  let t0 ← IO.monoMsNow
  let blocks ← IO.lazyPure fun _ => Ix.CondenseM.run (Ix.Compile.FrontEnd.graph env)
  let t1 ← IO.monoMsNow
  let parallel := (← IO.getEnv "IX_BD_SEQUENTIAL").isNone
  let stored := (← IO.getEnv "IX_BD_WALK_ALL").isNone
  let trace := ((← IO.getEnv "IX_BD_TRACE").map fun s => (s.splitOn ",").toArray).getD #[]
  return (← install env blocks workers parallel).map fun k =>
    { k with stored, trace, times := #[("condense", t1 - t0)] ++ k.times }

/-! ## The walk -/

/-- A context entry: a binder's free variable or a `let`'s annotated value, with
an identity for the sharing memo. -/
structure CtxEntry where
  id : Nat
  val : KExpr

/-- What a record's walk reads. `large` and `params` are the root's numbering
of level parameters (`Ix.LeanIngress.Numbering`): a large eliminator's source
numbers its motive universe last, the record numbers it first. -/
structure Cx where
  fe : FEnv .source
  core : Ix.Kernel.Cached.CoreFnsI .source
  sharing : Array Ixon.Expr
  bounds : Array Nat
  large : Bool := false
  params : Nat := 0
  /-- print why a datum is undecided (`IX_BD_TRACE`, for diagnosis) -/
  trace : Bool := false

/-- A source level parameter's index in the record's numbering (the inverse of
`Ix.LeanIngress.Numbering.pos`). -/
def Cx.recordParam (cx : Cx) (p : Nat) : Nat :=
  if cx.large then (if p + 1 == cx.params then 0 else p + 1) else p

/-- The node of a decided datum, its parameters in the record's numbering. -/
def Cx.nodeOf (cx : Cx) (pw : PropWhen) : Node :=
  match pw.toList? with
  | none => .binder none
  | some ps => .binder (some ((ps.map cx.recordParam).toArray.qsort (· < ·)))

/-- A record's walk state: the sharing entries' variants (by node list) and
blocks, and the memo of share sites under the same numbering and context. -/
structure WState where
  nextId : Nat := 0
  variants : Std.HashMap Nat (Std.HashMap (Array Node) Nat) := {}
  blocks : Array Block := #[]
  memo : Std.HashMap (Nat × Bool × List Nat) (KExpr × Nat × Bool) := {}
  /-- the stored walk's memo (`walkStored`): the variant of a share site -/
  memoS : Std.HashMap (Nat × Bool × List Nat) Nat := {}

abbrev WM := StateT WState CM
/-- An entry's walk: its nodes' data, by ordinal. -/
abbrev EM := StateT (Array Node) WM

/-- Bounds the walk's depth (the recursion is structural on it). -/
def walkFuel : Nat := 1 <<< 24

/-- The record and its source differ: the record gets the undecided section. -/
def mismatch (what : String) : EM α :=
  throw (.internal s!"binder data: the record and its source differ at {what}")

private def freshId : EM Nat :=
  modifyGetThe WState fun st => (st.nextId, { st with nextId := st.nextId + 1 })

private def reserve : EM Nat :=
  modifyGet fun nodes => (nodes.size, nodes.push (.binder none))

private def setNode (ord : Nat) (n : Node) : EM Unit :=
  modify fun nodes => nodes.set! ord n

/-- The variant of entry `n` for the node list `nodes`. -/
private def variantOf (n : Nat) (nodes : Array Node) : WM Nat := do
  let st ← get
  let table := st.variants.getD n {}
  match table[nodes]? with
  | some v => pure v
  | none =>
    let v := table.size
    set { st with variants := st.variants.insert n (table.insert nodes v)
                  blocks := st.blocks.push ⟨1, n, v, nodes⟩ }
    pure v

/-- IxC's datum of a run whose annotated opened leaf is `leaf` at `depth`
(`annotPwPiI` for a ∀ run, `annotPwLamI` for a λ run); `none` where IxC's
function fails. -/
def datum (cx : Cx) (pi : Bool) (depth : Nat) (leaf : KExpr) : EM (Option PropWhen) := do
  let act : CM PropWhen :=
    if pi then Ix.Kernel.Cached.annotPwPiI cx.core cx.fe depth leaf
    else Ix.Kernel.Cached.annotPwLamI cx.core cx.fe depth leaf
  let res : Option PropWhen ← (tryCatch (some <$> act) (fun e =>
      if cx.trace then
        dbgTrace s!"binder data trace: the datum of a {if pi then "∀" else "λ"} run at depth {depth} \
          fails: {traceError e}" fun _ => pure none
      else pure none) : CM (Option PropWhen))
  pure res

/-- A run of binders of one kind in both trees: each binder's domain in the
record and in the source, and its metadata (the record's contracts); then both
bodies. -/
def binderRun (pi : Bool) : Ixon.Expr → KExpr → Array (Ixon.Expr × KExpr × BinderMeta) →
    Ixon.Expr × KExpr × Array (Ixon.Expr × KExpr × BinderMeta)
  | e@(.lam c t b), x@(.lam ty body _), acc =>
    if pi then (e, x, acc) else binderRun pi b body (acc.push (t, ty, BinderMeta.ofContracts c .shared))
  | e@(.all c r t b), x@(.forallE ty body _), acc =>
    if pi then binderRun pi b body (acc.push (t, ty, BinderMeta.ofContracts c r)) else (e, x, acc)
  | e, x, acc => (e, x, acc)

/-- The datum of the `n`-th binder of a ∀-chain. -/
def forallDatumAt : Nat → KExpr → Option PropWhen
  | 0, .forallE _ _ mb => some mb.pw
  | n + 1, .forallE _ b _ => forallDatumAt n b
  | _, _ => none

/-- The walk of one entry's tree `e` beside its source `x`, under `ctx`
(innermost first) at binder depth `depth`: the annotated opened term, and
whether anything in it is undecided. Every numbered node of `e` gets its datum
at its ordinal.

`exp` is a definition value's annotated, decided type, given at the value's top
λ-chain: where IxC's datum function fails at a λ of that chain, the λ takes the
datum of the type's ∀ at the same place (binder congruence: a λ's codomain is
the type's codomain there, so its sort is that ∀'s), as IxC's pass over the
record does. -/
def walk : Nat → Cx → List CtxEntry → Nat → Option KExpr → Ixon.Expr → KExpr → EM (KExpr × Bool)
  | 0, _, _, _, _, _, _ => mismatch "the walk's depth bound"
  | fuel + 1, cx, ctx, depth, exp, e, x =>
    match e, x with
    | .var i, _ =>
      match ctx[i.toNat]? with
      | some c => pure (c.val, false)
      | none => mismatch "a loose variable"
    | .app f a, .app xf xa => do
      let (f', bf) ← walk fuel cx ctx depth none f xf
      let (a', ba) ← walk fuel cx ctx depth none a xa
      pure (.app f' a', bf || ba)
    | .lam .., .lam .. | .all .., .forallE .. => do
      let pi := e matches .all ..
      let (leafE, leafX, bs) := binderRun pi e x #[]
      let mut inner := ctx
      let mut ords : Array Nat := #[]
      let mut stk : List (Ix.Kernel.Cached.AnnotBinderEntry .source) := []
      let mut bad := false
      for h : j in [:bs.size] do
        let (t, ty, mb) := bs[j]
        ords := ords.push (← reserve)
        let (t', bt) ← walk fuel cx inner (depth + j) none t ty
        bad := bad || bt
        let id ← freshId
        inner := ⟨id, .fvar (depth + j) t'⟩ :: inner
        stk := (t', mb) :: stk
      let k := bs.size
      let (leaf', bl) ← walk fuel cx inner (depth + k) none leafE leafX
      let pw? ← datum cx pi (depth + k) leaf'
      let pw? := if pw?.isSome || pi then pw? else exp.bind (forallDatumAt (k - 1))
      let undecided := bad || bl || pw?.isNone
      let node : Node := if undecided then .undecided else cx.nodeOf (pw?.getD .never)
      for ord in ords do setNode ord node
      let mk : KExpr → KExpr → BinderMeta → KExpr :=
        if pi then fun ty b mb => .forallE ty b mb else fun ty b mb => .lam ty b mb
      let out ← (Ix.Kernel.Cached.annotateBindersOutI mk depth (some (pw?.getD .never)) stk (k - 1)
        (leaf'.abstractRangeC depth k) : CM KExpr)
      pure (out, undecided)
    | .letE _ t v b, .letE ty val body _ => do
      -- IxC annotates the type and the value, then the body with the value
      -- transparent (its ζ-reduct)
      let (_, bt) ← walk fuel cx ctx depth none t ty
      let (v', bv) ← walk fuel cx ctx depth none v val
      let id ← freshId
      let (b', bb) ← walk fuel cx (⟨id, v'⟩ :: ctx) depth exp b body
      pure (b', bt || bv || bb)
    | .prj _ _ v, .proj k i xv => do
      let (v', bv) ← walk fuel cx ctx depth none v xv
      pure (.proj k i v', bv)
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, cx.large, (ctx.take (cx.bounds[n]?.getD 0)).map (·.id))
      let (e', variant, bad) ← match (← getThe WState).memo[key]? with
        | some hit => pure hit
        | none => do
          let some entry := cx.sharing[n]? | mismatch "a share"
          let ((e', bad), nodes) ← ((walk fuel cx ctx depth none entry x).run #[] :
            WM ((KExpr × Bool) × Array Node))
          let variant ← variantOf n nodes
          modifyThe WState fun st => { st with memo := st.memo.insert key (e', variant, bad) }
          pure (e', variant, bad)
      setNode ord (.share variant)
      pure (e', bad)
    | .sort _, .sort _ | .ref .., .const .. | .recur .., .const .. | .str _, .lit _
    | .nat _, .lit _ => pure (x, false)
    | _, _ => mismatch "a node"

/-- The walk of one entry's tree `e` beside `k`, a term phase A annotated and
stored (IxC's annotation of the same source): every numbered node of `e` gets
the datum `k` carries at its place, and nothing is inferred. A node where the
trees differ is a mismatch, and so is a `let` (the annotation ζ-reduces it, so
its type's and value's data are not in `k`): the root is then walked by
`walk`. -/
def walkStored : Nat → Cx → List Nat → Ixon.Expr → KExpr → EM Unit
  | 0, _, _, _, _ => mismatch "the stored walk's depth bound"
  | fuel + 1, cx, ctx, e, k =>
    match e, k with
    | .var _, .bvar _ => pure ()
    | .app f a, .app kf ka => do
      walkStored fuel cx ctx f kf
      walkStored fuel cx ctx a ka
    | .lam _ t b, .lam ty body mb | .all _ _ t b, .forallE ty body mb => do
      let ord ← reserve
      setNode ord (cx.nodeOf mb.pw)
      walkStored fuel cx ctx t ty
      let id ← freshId
      walkStored fuel cx (id :: ctx) b body
    | .prj _ _ v, .proj _ _ kv => walkStored fuel cx ctx v kv
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      let key := (n, cx.large, ctx.take (cx.bounds[n]?.getD 0))
      let variant ← match (← getThe WState).memoS[key]? with
        | some v => pure v
        | none => do
          let some entry := cx.sharing[n]? | mismatch "a share"
          let ((), nodes) ← ((walkStored fuel cx ctx entry k).run #[] : WM (Unit × Array Node))
          let v ← variantOf n nodes
          modifyThe WState fun st => { st with memoS := st.memoS.insert key v }
          pure v
      setNode ord (.share variant)
    | .sort _, .sort _ | .ref .., .const .. | .recur .., .const .. | .str _, .lit _
    | .nat _, .lit _ => pure ()
    | _, _ => mismatch "a node of the stored term"

/-! ## A record's sources -/

/-- Whether a member of `c` is unsafe or partial. -/
def unsafeOrPartial (c : Ixon.Constant) : Bool :=
  let defn (d : Ixon.Definition) : Bool := match d.safety with
    | .safe => false
    | _ => true
  match c.info with
  | .defn d => defn d
  | .recr r => r.isUnsafe
  | .axio a => a.isUnsafe
  | .muts ms => ms.any fun
    | .defn d => defn d
    | .indc i => i.isUnsafe || i.ctors.any (·.isUnsafe)
    | .recr r => r.isUnsafe
  | _ => false

/-- The block's members, as the record lists them. -/
def members (c : Ixon.Constant) : Array (Ixon.MutConst ⊕ Ixon.ConstantInfo) :=
  match c.info with
  | .muts ms => ms.map .inl
  | info => #[.inr info]

/-- A source constant's root terms with their numberings, in section order, when
its kind is the record member's. -/
def sourceItems (find : Ix.Name → Option Ix.ConstantInfo) (ci : Ix.ConstantInfo) :
    Ixon.MutConst ⊕ Ixon.ConstantInfo → Option (Array (Numbering × Ix.Expr))
  | .inl (.defn _) | .inr (.defn _) =>
    let σ : Numbering := ⟨ci.getCnst.levelParams, false⟩
    match ci with
    | .defnInfo d => some #[(σ, d.cnst.type), (σ, d.value)]
    | .thmInfo t => some #[(σ, t.cnst.type), (σ, t.value)]
    | .opaqueInfo o => some #[(σ, o.cnst.type), (σ, o.value)]
    | _ => none
  | .inr (.axio _) => match ci with
    | .axiomInfo a => some #[(⟨a.cnst.levelParams, false⟩, a.cnst.type)]
    | _ => none
  | .inr (.quot _) => match ci with
    | .quotInfo q => some #[(⟨q.cnst.levelParams, false⟩, q.cnst.type)]
    | _ => none
  | .inl (.recr r) | .inr (.recr r) => match ci with
    | .recInfo v => do
      guard (v.rules.size == r.rules.size)
      let indLevels := match v.all[0]?.bind find with
        | some (.inductInfo i) => i.cnst.levelParams.size
        | _ => v.cnst.levelParams.size
      let σ : Numbering := ⟨v.cnst.levelParams, v.cnst.levelParams.size == indLevels + 1⟩
      some (#[(σ, v.cnst.type)] ++ v.rules.map ((σ, ·.rhs)))
    | _ => none
  | .inl (.indc i) => match ci with
    | .inductInfo v => do
      let σ : Numbering := ⟨v.cnst.levelParams, false⟩
      let ctors ← v.ctors.mapM fun n => match find n with
        | some (.ctorInfo k) => some (⟨k.cnst.levelParams, false⟩, k.cnst.type)
        | _ => none
      guard (ctors.size == i.ctors.size)
      some (#[(σ, v.cnst.type)] ++ ctors)
    | _ => none
  | _ => none

/-- The terms phase A annotated and stored for a record member's roots, in
section order, where it certainly annotated them: a definition's type and value
(not a pinned `Nat` operation's, which the ordinary step installs), a theorem's
and an opaque's type, an axiom's type. `none` elsewhere: a theorem's value is
stored raw, and blocks and quotients are walked. -/
def storedItems (fe : FEnv .source) (n : Ix.Name) :
    Ixon.MutConst ⊕ Ixon.ConstantInfo → Array (Option KExpr)
  | .inl (.defn _) | .inr (.defn _) =>
    let key := ingressKey n
    match fe.find? key with
    | some (.defnInfo cv v _) =>
      if Ix.Kernel.natOpNames.contains key || Ix.Kernel.natDivModNames.contains key then #[none, none]
      else #[some cv.type, some v]
    | some (.thmInfo cv _) => #[some cv.type, none]
    | some (.axiomInfo cv) => #[some cv.type, none]
    | _ => #[none, none]
  | .inr (.axio _) => match fe.find? (ingressKey n) with
    | some (.axiomInfo cv) => #[some cv.type]
    | _ => #[none]
  | .inl (.recr r) | .inr (.recr r) => Array.replicate (1 + r.rules.size) none
  | .inl (.indc i) => Array.replicate (1 + i.ctors.size) none
  | .inr (.quot _) => #[none]
  | .inr _ => #[]

/-- The Source roots of a record, from its members' sources (`extra` first,
then the compile's input), each with the numbering of its level parameters. -/
def sourceRoots (env : Ix.Environment) (extra : Array (Ix.Name × Ix.ConstantInfo))
    (names : Array Ix.Name) (c : Ixon.Constant) : Option (Array (KExpr × Numbering)) := do
  let ms := members c
  guard (ms.size == names.size)
  let find (n : Ix.Name) : Option Ix.ConstantInfo :=
    ((extra.find? (·.1 == n)).map (·.2)).orElse fun _ => env.consts.get? n
  let mut items : Array (Numbering × Ix.Expr) := #[]
  for (m, n) in ms.zip names do
    let ci ← find n
    items := items ++ (← sourceItems find ci m)
  let roots := (exprsOf items).toOption
  let roots ← roots
  guard (roots.size == (IxVM.PwHints.roots c).size && roots.size == items.size)
  return roots.zip (items.map (·.1))

/-! ## The annotator -/

/-- **The section of a block record**, from its members' sources: IxC's pass
over each root beside its source, against the installed environment. -/
def annotate (k : Installed) (extra : Array (Ix.Name × Ix.ConstantInfo)) (names : Array Ix.Name)
    (c : Ixon.Constant) : Array Ixon.BinderBlock :=
  let rs := IxVM.PwHints.roots c
  if rs.isEmpty then #[] else
  if unsafeOrPartial c then Ix.CompileM.undecidedSection c else
  match sourceRoots k.env extra names c with
  | none => Ix.CompileM.undecidedSection c
  | some xs =>
    let traced := !k.trace.isEmpty && names.any fun n => k.trace.contains n.pretty
    let cx0 : Cx := { fe := k.fe, core := k.core, sharing := c.sharing,
                      bounds := IxVM.PwHints.bounds c.sharing, trace := traced }
    let stored : Array (Option KExpr) := if !k.stored then #[] else
      ((members c).zip names).foldl (fun acc (m, n) => acc ++ storedItems k.fe n m) #[]
    let tys := IxVM.PwHints.valueTypes c
    let act : WM (Array Block) := do
      let mut out := #[]
      -- each root's annotated term, where nothing in it is undecided
      let mut annotated : Array (Option KExpr) := #[]
      for h : i in [:rs.size] do
        let some (x, σ) := xs[i]? | throw (.internal "binder data: a root without a source")
        let cx := { cx0 with large := σ.large, params := σ.names.size }
        -- the stored term's data where phase A annotated the root, else the walk
        let read : Option (Array Node) ← match stored[i]? with
          | some (some kx) =>
            tryCatch (do
                let ((), nodes) ← (walkStored walkFuel cx [] rs[i] kx).run #[]
                pure (some nodes))
              (fun _ => pure none)
          | _ => pure none
        let exp : Option KExpr := match tys[i]? with
          | some (some j) => annotated[j]?.join
          | _ => none
        let (nodes, kx?) ← match read, stored[i]? with
          | some nodes, some kx => pure (nodes, kx)
          | _, _ => do
            let ((kx, bad), nodes) ← (walk walkFuel cx [] 0 exp rs[i] x).run #[]
            pure (nodes, if bad then none else some kx)
        annotated := annotated.push kx?
        out := out.push ⟨0, i, 0, nodes⟩
      return out
    match (act.run {}).run {} with
    | .ok ((roots, st), _) =>
      match Ix.Compile.BinderData.sectionOf c (roots ++ st.blocks) with
      | .ok s => s
      | .error _ => Ix.CompileM.undecidedSection c
    | .error e =>
      if traced then
        dbgTrace s!"binder data trace: {names.map (·.pretty)}: the walk fails: {traceError e}"
          fun _ => Ix.CompileM.undecidedSection c
      else Ix.CompileM.undecidedSection c

/-- **The annotator of a compile** over its installed input. -/
def annotator (k : Installed) : Ix.BinderAnnotator :=
  { run := annotate k }

/-- The safe records of `env` whose section has an undecided binder, by address. -/
def undecidedSafe (env : Ixon.Env) (workers : Nat := 32) : Array Address :=
  let records : Array (Address × Ixon.LazyConstant) := env.consts.toArray
  (Ix.Compile.Parallel.map (max workers 1) (fun (a, lc) =>
    match lc.get? with
    | some c =>
      if !unsafeOrPartial c && c.binders.any (·.nodes.any (· == .undecided)) then some a else none
    | none => none) records).filterMap id

end Ix.Compile.KernelAnnotate

end
