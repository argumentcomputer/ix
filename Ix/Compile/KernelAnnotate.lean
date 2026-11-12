module

public import Ix.LeanIngress
public import Ix.KernelCheck.Step
public import Ix.Compile.BinderData
public import Ix.Compile.BinderRead
public import Ix.Compile.Parallel
public import Ix.Compile.FrontEnd
public import Ix.CompileM
public import Ix.KernelDisplay.Render

public section

/-!
# The compiler's binder-data annotator: IxC's pass over the Lean source

`ix compile` writes every block record's binder-data section while it builds
the record, before the record is hashed (`Ix.CompileM.withBinderSection`). This
module is the annotator it runs there. The data are IxC's: its annotation pass
(`annotateBodyI`, its telescope loops `annotatePisI`/`annotateLamsI`) writes at
every binder the zero-ness of the codomain sort, by `annotPwPiI`/`annotPwLamI`
on the annotated opened body; nothing here infers anything itself.

**The reading first.** Most records show every binder's datum in their Lean
source without inference (`Ix.Compile.BinderRead`: a ∀-body's sort from its
head's declared type, a λ-run's from the sort of the type it stands at); those
records are read and never walked. The rest are walked as below.

**The environment.** Before the compile, the constants whose source does not
read are found (`Ix.Compile.BinderRead.sourceReads`: the records the walk will
see), and IxC ingests their install closure (`restrictClosure`) from the
compile's own input in Source mode (`Ix.LeanIngress`: every constant keyed by its
Lean name, or its role's key) and installs it with phase A of its fold
(`annotDeclStepWithUserAxioms`, at the committed bundle's evidence), once, in
dependency order (`install`), a wave of the dependency levels at a time on workers
that each build an environment of their own (`phaseAWorkers`). Unsafe and partial
groups go through the typing
tier; a declaration that fails is retried after them, and one refused again
(a compiler-trust axiom, say) enters without its checks, with its
annotated type (`lenient`); a structure the install leaves without a projection
table gets one (`addTables`). The installed
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
share is walked once per context of the variables it can name and per source
term (content-equal constants, `HAdd` and `HSub` say, share one record entry and
differ in the source). IxC's core runs at `annotatorMode`; where its datum
function fails at a λ-run, the run takes the zero-ness of the sort of the type it
stands at (`Expect`). Each record's
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

/-- The mode IxC's core runs at for the annotator. The annotation pass is the
same at both modes (it is ungated). At `.verified` its certificates re-check
every argument, β-redex and projection the walk builds, so a term the walk got
wrong shows as an undecided binder rather than as a datum. -/
def annotatorMode : Ix.Kernel.CheckMode := .verified

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
  /-- whether the walk memoizes share sites (`IX_BD_NOMEMO` turns it off, for diagnosis) -/
  memo : Bool := true
  /-- whether the syntactic reading is measured beside the walk (`IX_BD_TIER1`) -/
  tier1 : Bool := false
  /-- whether each record's route (the source reading or the walk) is printed
  (`IX_BD_T1STAT`, for measurement) -/
  t1stat : Bool := false
  /-- whether every record is walked, the source reading off (`IX_BD_NOREAD`, for the
  cross-check of the reading against IxC's pass) -/
  noread : Bool := false
  /-- whether a record the source reading does not decide gets the undecided section
  instead of the walk (`IX_BD_READONLY`, for measurement) -/
  readonly : Bool := false
  /-- projection tables added for structures the install left without one, and
  those skipped because the structure is a proposition -/
  tablesAdded : Nat := 0
  tablesProp : Nat := 0
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
def step (mode : Ix.Kernel.CheckMode) (ev : Ix.Kernel.Evidences .source) (fe : FEnv .source) (pos : Nat)
    (d : Ix.Kernel.Declaration .source) :
    FEnv .source × Nat × Option (Ix.Kernel.CheckError .source) :=
  let before := fe.env
  match Ix.Kernel.Cached.annotDeclStepWithUserAxioms mode ev (pos, fe, #[]) d {} with
  | .ok ((pos', fe', _), _) => (fe', pos', none)
  | .error (e, _) => (reindex before, pos + 1, some e)

/-- A declaration the kernel refuses, entered without its checks: its constant
with its annotated type (and a definition's annotated value, so that it
unfolds; a theorem keeps its value, which nothing reduces), as phase A would
have pushed it. The annotation is IxC's (`annotConstantValC`, `annotValueC`);
only the step's policy and checks are skipped. `none` where the annotation
itself fails. The data are not checked here: the annotator is not trusted. -/
def lenient (mode : Ix.Kernel.CheckMode) (fe : FEnv .source)
    (d : Ix.Kernel.Declaration .source) : Option (FEnv .source) :=
  let run {α : Type} (act : CM α) : Option α := match act.run {} with
    | .ok (a, _) => some a
    | .error _ => none
  match d with
  | .axiomDecl cv =>
    (run (Ix.Kernel.Cached.annotConstantValC mode fe cv)).map fun r => fe.push (.axiomInfo r.1)
  | .opaqueDecl cv _ =>
    (run (Ix.Kernel.Cached.annotConstantValC mode fe cv)).map fun r => fe.push (.axiomInfo r.1)
  | .thmDecl cv v =>
    (run (Ix.Kernel.Cached.annotConstantValC mode fe cv)).map fun r => fe.push (.thmInfo r.1 v)
  | .defnDecl cv v h =>
    (run (Ix.Kernel.Cached.annotValueC mode fe cv v)).map fun r =>
      fe.push (.defnInfo r.1 r.2.2 h)
  | .indDecl block _ => lenientBlock mode fe block
  | _ => none
where
  /-- An inductive block's constants in order (its types, constructors and
  recursors), each type and rule right-hand side annotated by IxC's pass
  against what is installed before it; no checks, no generated recursors or
  projection tables (`addTables` adds the tables). -/
  lenientBlock (mode : Ix.Kernel.CheckMode) (fe : FEnv .source)
      (block : List (Ix.Kernel.ConstantInfo .source)) : Option (FEnv .source) := Id.run do
    let mut fe := fe
    for ci in block do
      let core := Ix.Kernel.Cached.coreKnotI mode fe Ix.Kernel.checkFuel
      let ann (e : KExpr) : Option KExpr := match (core.annotate 0 e).run {} with
        | .ok (a, _) => some a
        | .error _ => none
      let cv := ci.toConstantVal
      let some ty := ann cv.type | return none
      let cv' := { cv with type := ty }
      match ci with
      | .indInfo _ caps => fe := fe.push (.indInfo cv' caps)
      | .ctorInfo _ nP nF => fe := fe.push (.ctorInfo cv' nP nF)
      | .recInfo _ m p rules =>
        let some rules' := rules.mapM (fun r => (ann r.rhs).map fun rhs => { r with rhs }) | return none
        fe := fe.push (.recInfo cv' m p rules')
      | ci => fe := fe.push ci
    return some fe

/-- **Projection tables for the structures the install left without one**: every
one-constructor, index-free inductive of `env` with fields, whose type former
and constructor are installed and whose projection table is not (a nested or
mutual structure, which IxC models rather than installs natively, or a block
entered by `lenient`). Lean's kernel types `.proj S i e` at every such `S`. The
table is built as IxC's native route builds it: the bodies from the
constructor's annotated type (`structProjBodiesC`), the parent's result sort
from its type former's type. A propositional structure is left out (its
guards need the fields' sorts): the count of those is returned too. -/
def addTables (env : Ix.Environment) (fe : FEnv .source) : FEnv .source × Nat × Nat := Id.run do
  let mut fe := fe
  let mut added := 0
  let mut prop := 0
  for (_, ci) in env.consts do
    let .inductInfo v := ci | continue
    unless v.numIndices == 0 && v.ctors.size == 1 && !v.isUnsafe do continue
    let some c := v.ctors[0]? | continue
    let T := ingressKey v.cnst.name
    let C := ingressKey c
    if (fe.findProj? T 0).isSome then continue
    let (some (.indInfo cvT _), some (.ctorInfo cvC nP nF)) := (fe.find? T, fe.find? C) | continue
    if nF == 0 then continue
    let some bodies := Ix.Kernel.Cached.structProjBodiesC T nP nF cvC.type | continue
    let .sort u := Ix.Kernel.Expr.piResult cvT.type | continue
    if Ix.Kernel.Level.isEquiv u .zero == some true then
      prop := prop + 1
      continue
    fe := fe.push (.projInfo ⟨T, cvT.levelParams, nP, C, nF, u, bodies, List.replicate nF u, 0⟩)
    added := added + 1
  return (fe, added, prop)

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
declaration takes the ordinary step. -/
def separable (mode : Ix.Kernel.CheckMode) (fe : FEnv .source) (d : CDecl .source) : Option (Ix.Kernel.ConstantInfo .source) :=
  let run {α : Type} (act : CM α) : Option α := match act.run {} with
    | .ok (a, _) => some a
    | .error _ => none
  if d.anchorMismatch?.isSome then none else
  match d with
  | .defnDecl cv v h =>
    if Ix.Kernel.natOpNames.contains cv.name || Ix.Kernel.natDivModNames.contains cv.name then none
    else (run (Ix.Kernel.Cached.annotValueC mode fe cv v)).map fun r => .defnInfo r.1 r.2.2 h
  | .thmDecl cv v =>
    (run (Ix.Kernel.Cached.annotConstantValC mode fe cv)).map fun r => .thmInfo r.1 v
  | .opaqueDecl cv v =>
    (run (Ix.Kernel.Cached.annotValueC mode fe cv v)).map fun r => .axiomInfo r.1
  | _ => none

/-- A declaration's pushes computed ahead against `fe` (`separable`'s). A
declaration that is not separable (a block, an axiom, a pinned `Nat` operation)
takes the ordinary step in turn: run ahead, its first push would copy the
index every task shares, a cost that grows with the environment. -/
def pushesAhead (mode : Ix.Kernel.CheckMode) (fe : FEnv .source) (d : CDecl .source) :
    Option (Array (Ix.Kernel.ConstantInfo .source)) :=
  (separable mode fe d).map (#[·])

/-- Whether every constant a definition, theorem, opaque or axiom names is
installed (`constsResolveFC`). One that names a missing constant would fail
its step, and a failed step rebuilds the index (`reindex`), so it goes to the
retry list without a step. -/
def resolves (fe : FEnv .source) (d : CDecl .source) : Bool :=
  match d with
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
    Ix.Kernel.Cached.constsResolveFC fe cv.type && Ix.Kernel.Cached.constsResolveFC fe v
  | .axiomDecl cv => Ix.Kernel.Cached.constsResolveFC fe cv.type
  | _ => true

/-- Whether `separable` applies to a declaration's kind: a definition other than a
pinned `Nat` operation, a theorem, an opaque. -/
def separableKind : CDecl .source → Bool
  | .defnDecl cv _ _ => !(Ix.Kernel.natOpNames.contains cv.name || Ix.Kernel.natDivModNames.contains cv.name)
  | .thmDecl .. | .opaqueDecl .. => true
  | _ => false

/-- What a worker made of a declaration of a wave, against its own environment:
the constants to push (a separable declaration's, annotated against it; an ordinary
step's pushes, already in that worker's environment), or a retry after the waves (it
names a constant not installed, or its annotation or step fails). -/
inductive Made where
  | pushes (cis : Array (Ix.Kernel.ConstantInfo .source))
  | retry
  deriving Inhabited

/-- One declaration on a worker's environment `fe` (`pos`, its fold position): the
environment after it (an ordinary step's, which pushes; `fe` itself otherwise) and
what was made. -/
def makeOne (mode : Ix.Kernel.CheckMode) (ev : Ix.Kernel.Evidences .source) (fe : FEnv .source)
    (pos : Nat) (d : CDecl .source) : FEnv .source × Made :=
  if !resolves fe d then (fe, .retry)
  else if separableKind d then
    match separable mode fe d with
    | some ci => (fe, .pushes #[ci])
    | none => (fe, .retry)
  else
    let vis := fe.visibleBelow
    let (fe', _, err) := step mode ev fe pos d
    match err with
    | none => (fe', .pushes (fe'.env.consts.take (fe'.visibleBelow - vis)).reverse.toArray)
    | some _ => (fe', .retry)

/-- **Phase A on workers**, each with an environment of its own built by `push`
(never shared, so every push is in place). The prelude's wave (wave 0, whose
declarations name each other) is made whole by every worker, in order. At every
other wave, worker `w` makes the declarations of the groups `g` with `g % W = w`
(`groupOf`, by position in `prepared`; a group's declarations, which may name each
other, in order on one worker), each against its own environment (`makeOne`) and
pushed there at once, publishes them, and pushes every other worker's (in worker
order, a constant already there skipped). The groups of a wave do not name each
other, so each declaration is made against an environment that answers its lookups
as the one-by-one fold's does. The first worker's environment, and the
declarations to retry (in wave order, then worker order). -/
def phaseAWorkers (mode : Ix.Kernel.CheckMode) (ev : Ix.Kernel.Evidences .source)
    (prepared : Array (CDecl .source)) (groupOf : Array Nat) (waves : Array (Array Nat))
    (workers : Nat) : IO (FEnv .source × Array Nat) := do
  let W := max 1 workers
  -- worker `w`'s results at wave `k`, at `k * W + w`
  let mut outs : Array (IO.Promise (Array (Nat × Made))) := #[]
  for _ in [:waves.size * W] do
    outs := outs.push (← IO.Promise.new)
  let outs := outs
  let run (w : Nat) : IO (FEnv .source × Array Nat) := do
    let mut fe : FEnv .source := Ix.Kernel.mkFEnv Ix.Kernel.Env.empty
    let mut retry : Array Nat := #[]
    for h : k in [:waves.size] do
      let wave := waves[k]
      let mut mine : Array (Nat × Made) := #[]
      for i in wave do
        unless k == 0 || (groupOf[i]?.getD i) % W == w do continue
        let (fe', m) := makeOne mode ev fe i prepared[i]!
        fe := fe'
        match m with
        | .pushes cis =>
          -- read by every worker, written by none: no reference counts
          let mut ps : Array (Ix.Kernel.ConstantInfo .source) := #[]
          for ci in cis do
            let mut ci := ci
            if k != 0 then
              ci ← (unsafe Runtime.markPersistent ci : BaseIO (Ix.Kernel.ConstantInfo .source))
            if (fe.find? ci.name).isNone then fe := fe.push ci
            ps := ps.push ci
          mine := mine.push (i, .pushes ps)
        | .retry =>
          mine := mine.push (i, .retry)
          if k == 0 && w == 0 then retry := retry.push i
      if k == 0 then continue
      if let some p := outs[k * W + w]? then p.resolve mine
      for w' in [:W] do
        let rs : Array (Nat × Made) ← if w' == w then pure mine else
          match outs[k * W + w']? with
          | some p => (monadLift (IO.wait p.result!) : IO (Array (Nat × Made)))
          | none => pure #[]
        for (i, m) in rs do
          match m with
          | .pushes cis =>
            if w' != w then
              for ci in cis do
                if (fe.find? ci.name).isNone then fe := fe.push ci
          | .retry => if w == 0 then retry := retry.push i
    return (fe, retry)
  let mut tasks := #[]
  for w in [:W] do
    tasks := tasks.push (← IO.asTask (run w) (prio := .dedicated))
  let mut first : Option (FEnv .source × Array Nat) := none
  for t in tasks do
    let r ← IO.ofExcept (← IO.wait t)
    if first.isNone then first := some r
  match first with
  | some r => return r
  | none => return (Ix.Kernel.mkFEnv Ix.Kernel.Env.empty, #[])

/-- A kernel error on one line, for `IX_BD_TRACE`. -/
def traceError (e : Ix.Kernel.CheckError .source) : String :=
  ((Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2.replace "\n" " ").take 400 |>.toString

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

/-- The structures a term projects from (`IX_BD_TRACE`'s diagnosis). -/
def projKeys (e : KExpr) : Array (Ix.Kernel.Key .source) := Id.run do
  let mut seen : Std.HashSet KExpr := {}
  let mut todo := #[e]
  let mut out := #[]
  while h : todo.size > 0 do
    let e := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .proj k _ x => out := out.push k; todo := todo.push x
    | .app f a => todo := todo.push f |>.push a
    | .lam t b _ | .forallE t b _ => todo := todo.push t |>.push b
    | .letE t v b _ => todo := todo.push t |>.push v |>.push b
    | _ => pure ()
  return out

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
    (parallel : Bool := true) (trace : Bool := false) (persist : Bool := true)
    (onWorkers : Bool := true) :
    IO (Except String Installed) := do
  let mode := annotatorMode
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
  let mut groupKey : Std.HashMap (Ix.Kernel.Key .source) Nat := {}
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
        if let some k := d.names.head? then
          levelOf := levelOf.insert k glevel[gi]!
          groupKey := groupKey.insert k gi
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
  if onWorkers then
    let n0 ← IO.monoNanosNow
    -- each declaration's group, by position in `prepared`
    let mut groupOf : Array Nat := Array.mkEmpty prepared.size
    for h : i in [:prepared.size] do
      groupOf := groupOf.push ((prepared[i].names.head?.bind (groupKey[·]?)).getD i)
    let (feW, again) ← phaseAWorkers mode ev prepared groupOf waves workers
    nsStep := (← IO.monoNanosNow) - n0
    fe := feW
    pos := prepared.size
    ok := prepared.size - again.size
    retry := again.map (prepared[·]!)
  -- (`IX_BD_WAVES`, for measurement: phase A on one environment, its waves' separable
  -- declarations annotated ahead)
  for wave in (if onWorkers then #[] else waves) do
    -- the wave's separable declarations, annotated against the environment as
    -- it stands before the wave (`separable`)
    let base := fe
    let n0 ← IO.monoNanosNow
    let pushes : Array (Option (Array (Ix.Kernel.ConstantInfo .source))) ← IO.lazyPure fun _ =>
      if !parallel || wave.size < 8 then wave.map fun _ => none
      else Ix.Compile.Parallel.map (4 * max workers 1) (fun i => pushesAhead mode base prepared[i]!) wave
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
      if !resolves fe d then
        retry := retry.push d
        pos := pos + 1
        continue
      let m0 ← IO.monoNanosNow
      let (fe', pos', err) ← IO.lazyPure fun _ => step mode ev fe pos d
      nsStep := nsStep + ((← IO.monoNanosNow) - m0)
      fe := fe'
      pos := pos'
      match err with
      | none => ok := ok + 1
      | some _ => retry := retry.push d
  let t4 ← IO.monoMsNow
  let retried := retry.size
  let tiered := tiers.size
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
    if !resolves fe d then
      failures := failures.push (declName d, "names a constant that is not installed")
      pos := pos + 1
      continue
    let (fe', pos', err) := step mode ev fe pos d
    fe := fe'
    pos := pos'
    match err with
    | none => ok := ok + 1
    | some e =>
      let why := (Benchmarks.Kernel.CheckIxeStep.checkOutcome e).2
      failures := failures.push (declName d, why)
      if let some fe' := lenient mode fe d then
        fe := fe'
        lenientCount := lenientCount + 1
  -- projection tables for the structures left without one
  let (feT, tablesAdded, tablesProp) := addTables env fe
  fe := feT
  let t5 ← IO.monoMsNow
  -- marked persistent: every worker reads them, none writes them, and their reference
  -- counts are never touched (`IX_BD_NOPERSIST` leaves them ordinary shared objects, for
  -- measurement)
  let shared ← if persist then (unsafe Runtime.markPersistent fe : BaseIO (FEnv .source)) else pure fe
  let core0 := Ix.Kernel.Cached.coreKnotI mode shared Ix.Kernel.checkFuel
  let core ← if persist then (unsafe Runtime.markPersistent core0 : BaseIO (Ix.Kernel.Cached.CoreFnsI .source))
    else pure core0
  let t6 ← IO.monoMsNow
  if trace then
    -- the structures some installed term projects from that have no projection table
    let mut seen : Std.HashSet (Ix.Kernel.Key .source) := {}
    let mut shown := 0
    for ci in shared.env.consts do
      let terms : List KExpr := match ci with
        | .defnInfo cv v _ => [cv.type, v]
        | .thmInfo cv v => [cv.type, v]
        | ci => [ci.toConstantVal.type]
      for t in terms do
        for k in projKeys t do
          if !seen.contains k then
            seen := seen.insert k
            if (shared.findProj? k 0).isNone && shown < 40 then
              shown := shown + 1
              IO.eprintln s!"binder data trace: {ci.toConstantVal.name} projects from {k}, which has no projection table"

  return .ok { fe := shared, core, env, installed := ok, failures, lenient := lenientCount,
               ahead, waves := waves.size, tablesAdded, tablesProp,
               times := #[("prelude", tPre - t0), ("groups", tGroups - tPre), ("convert", tConv - tGroups),
                 ("graph", tGraph - tConv), ("schedule", t1 - tGraph), ("lower", t2 - t1), ("canon", tCanon - t2), ("prepare", tPrep - tCanon), ("evidence", t3 - tPrep),
                 ("phaseA", t4 - t3), ("A:ahead", nsAhead / 1000000), ("A:push", nsPush / 1000000),
                 ("A:step", nsStep / 1000000), ("retried (count)", retried), ("tier (count)", tiered),
                 ("tier+retry", t5 - t4), ("persist", t6 - t5),
                 ("tables added (count)", tablesAdded), ("tables of propositions (count)", tablesProp)] }

/-! ## The install's restriction -/

/-- The constants a source term names, through its shared subterms once. -/
def exprRefs (e : Ix.Expr) (st : Std.HashSet Address × Std.HashSet Ix.Name) :
    Std.HashSet Address × Std.HashSet Ix.Name :=
  if st.1.contains e.getHash then st else
  let st := (st.1.insert e.getHash, st.2)
  match e with
  | .const n _ _ => (st.1, st.2.insert n)
  | .app f a _ => exprRefs a (exprRefs f st)
  | .lam _ t b _ _ => exprRefs b (exprRefs t st)
  | .forallE _ t b _ _ => exprRefs b (exprRefs t st)
  | .letE _ t v b _ _ => exprRefs b (exprRefs v (exprRefs t st))
  | .mdata _ x _ => exprRefs x st
  | .proj n _ x _ => exprRefs x (st.1, st.2.insert n)
  | _ => st
termination_by structural e

/-- **The install closure of the walked records `seeds`**: every constant their
whole terms name, then what installing each constant reached needs: a theorem's
type (nothing reduces its value), a definition's or an opaque's type and value,
any other constant's type and terms, and an inductive group whole (its types,
constructors and recursors). The role constants' closure (`Ix.Kernel.Key.ofName`:
the anchors and the pinned operations) is kept whole, theorems' proofs included:
installing a pinned operation reads the reference closure of its value and its
dependencies' roles, which its certificate ground must lie in
(`Ix.Kernel.evidenceLocal`). The closure, and that whole part of it. -/
def restrictClosure (env : Ix.Environment) (seeds : Array Ix.Name) (workers : Nat := 32) :
    Std.HashSet Ix.Name × Std.HashSet Ix.Name := Id.run do
  let mut recsOf : Std.HashMap Ix.Name (Array Ix.Name) := {}
  for (n, ci) in env.consts do
    if let .recInfo r := ci then
      if let some first := r.all[0]? then recsOf := recsOf.insert first ((recsOf.getD first #[]).push n)
  let groupNames (first : Ix.Name) : Array Ix.Name :=
    match env.consts.get? first with
    | some (.inductInfo v) =>
      v.all ++ v.all.flatMap (fun t => match env.consts.get? t with
        | some (.inductInfo w) => w.ctors
        | _ => #[]) ++ recsOf.getD first #[]
    | _ => #[]
  let firstOf (ci : Ix.ConstantInfo) : Option Ix.Name := match ci with
    | .inductInfo v => v.all[0]?
    | .ctorInfo c => match env.consts.get? c.induct with
      | some (.inductInfo v) => v.all[0]?
      | _ => none
    | .recInfo r => r.all[0]?
    | _ => none
  let needs (whole : Bool) (ci : Ix.ConstantInfo) : Std.HashSet Ix.Name :=
    let terms : Array Ix.Expr := match ci with
      | .defnInfo d => #[d.cnst.type, d.value]
      | .opaqueInfo o => #[o.cnst.type, o.value]
      | .thmInfo t => if whole then #[t.cnst.type, t.value] else #[t.cnst.type]
      | .recInfo r => #[r.cnst.type] ++ r.rules.map (·.rhs)
      | ci => #[ci.getCnst.type]
    let refs := (terms.foldl (fun st t => exprRefs t st) ({}, {})).2
    match firstOf ci with
    | some first => (groupNames first).foldl (·.insert ·) refs
    | none => refs
  -- breadth first, each level's needs on `workers` tasks
  let needsOf (whole : Bool) (n : Ix.Name) : Std.HashSet Ix.Name :=
    match env.consts.get? n with
    | some ci => needs whole ci
    | none => {}
  -- the role constants' closure, whole
  let roles := env.consts.fold (init := #[]) fun acc n _ => match ingressKey n with
    | .role _ => acc.push n
    | _ => acc
  let mut whole : Std.HashSet Ix.Name := {}
  for s in roles do whole := whole.insert s
  let mut level : Array (Std.HashSet Ix.Name) := Ix.Compile.Parallel.map workers (needsOf true) roles
  while !level.isEmpty do
    let mut next : Array Ix.Name := #[]
    for refs in level do
      for r in refs do
        unless whole.contains r do
          whole := whole.insert r
          next := next.push r
    level := Ix.Compile.Parallel.map workers (needsOf true) next
  -- the walked records' closure beside it
  let mut seen : Std.HashSet Ix.Name := whole
  let roots := seeds.filter fun s => env.consts.contains s && !whole.contains s
  for s in roots do seen := seen.insert s
  level := Ix.Compile.Parallel.map workers (needsOf true) roots
  while !level.isEmpty do
    let mut next : Array Ix.Name := #[]
    for refs in level do
      for r in refs do
        unless seen.contains r do
          seen := seen.insert r
          next := next.push r
    level := Ix.Compile.Parallel.map workers (needsOf false) next
  return (seen, whole)

/-- **Install a compile's input**: its condensation (`Ix.CondenseM`, as the
compile's front end builds it), then `install`. For measurement (the data are
the same): with `IX_BD_SEQUENTIAL` set phase A takes every step in turn, with
`IX_BD_WALK_ALL` every root is walked, with `IX_BD_WAVES` phase A runs on one
environment (its waves' separable declarations annotated ahead). -/
def installInput (env : Ix.Environment) (workers : Nat := 32) : IO (Except String Installed) := do
  -- only the install closure (`restrictClosure`) of the constants whose source does
  -- not read (`Ix.Compile.BinderRead.sourceReads`: the records the walk will see) is
  -- installed, theorems with a placeholder value (nothing reads a theorem's value);
  -- the sources stay the input's. For measurement: `IX_BD_RESTRICT` names the
  -- records in a file instead, one per line; `IX_BD_FULL` (and `IX_BD_NOREAD`, which
  -- walks every record) installs the whole input
  let width := 4 * max workers 1
  let tc0 ← IO.monoMsNow
  let full := (← IO.getEnv "IX_BD_FULL").isSome || (← IO.getEnv "IX_BD_NOREAD").isSome
  let seeds? : Option (Array Ix.Name) ← match (← IO.getEnv "IX_BD_RESTRICT") with
    | some path => do
      let keep : Std.HashSet String := (← IO.FS.lines path).foldl (·.insert ·) {}
      pure (some (env.consts.fold (init := #[]) fun acc n _ => if keep.contains n.pretty then acc.push n else acc))
    | none =>
      if full then pure none else do
        let find : Ix.Compile.BinderRead.Find := fun n => env.consts.get? n
        let unread ← IO.lazyPure fun _ => Ix.Compile.Parallel.map width
          (fun (nc : Ix.Name × Ix.ConstantInfo) =>
            if Ix.Compile.BinderRead.sourceReads find nc.2 then none else some nc.1) env.consts.toArray
        pure (some (unread.filterMap id))
  let tcP ← IO.monoMsNow
  let envI ← match seeds? with
    | some seeds => do
      let (closure, whole) ← IO.lazyPure fun _ => restrictClosure env seeds width
      -- a theorem outside the whole part, with a placeholder value
      let blank (n : Ix.Name) : Ix.ConstantInfo → Ix.ConstantInfo
        | .thmInfo t =>
          if whole.contains n then .thmInfo t else .thmInfo { t with value := Ix.Expr.mkSort Ix.Level.mkZero }
        | ci => ci
      pure { env with consts := env.consts.fold (init := {}) fun m n ci =>
        if closure.contains n then m.insert n (blank n ci) else m }
    | none => pure env
  let seedCount := (seeds?.map (·.size)).getD env.consts.size
  -- (measurement, with `IX_BD_T1STAT`) the seeds, one a line
  if (← IO.getEnv "IX_BD_T1STAT").isSome then
    for n in seeds?.getD #[] do IO.eprintln s!"BDSEED {n.pretty}"
  let tc1 ← IO.monoMsNow
  let t0 ← IO.monoMsNow
  let blocks ← IO.lazyPure fun _ => Ix.CondenseM.run (Ix.Compile.FrontEnd.graph envI)
  let t1 ← IO.monoMsNow
  let parallel := (← IO.getEnv "IX_BD_SEQUENTIAL").isNone
  let stored := (← IO.getEnv "IX_BD_WALK_ALL").isNone
  let memo := (← IO.getEnv "IX_BD_NOMEMO").isNone
  let trace := ((← IO.getEnv "IX_BD_TRACE").map fun s => (s.splitOn ",").toArray).getD #[]
  let tier1 := (← IO.getEnv "IX_BD_TIER1").isSome
  let t1stat := (← IO.getEnv "IX_BD_T1STAT").isSome
  let noread := (← IO.getEnv "IX_BD_NOREAD").isSome
  let readonly := (← IO.getEnv "IX_BD_READONLY").isSome
  let persist := (← IO.getEnv "IX_BD_NOPERSIST").isNone
  let onWorkers := (← IO.getEnv "IX_BD_WAVES").isNone
  return (← install envI blocks workers parallel (!trace.isEmpty) persist onWorkers).map fun k =>
    { k with env, stored, memo, trace, tier1, t1stat, noread, readonly,
             times := #[("seeds (count)", seedCount), ("installed constants (count)", envI.consts.size),
               ("prediction", tcP - tc0), ("restriction", tc1 - tcP),
               ("condense", t1 - t0)] ++ k.times }

/-! ## The walk -/

/-- A context entry: a binder's free variable or a `let`'s annotated value, with
an identity for the sharing memo. -/
structure CtxEntry where
  id : Nat
  val : KExpr
  /-- its type (a binder's annotated domain, a `let`'s annotated type), for the syntactic
  reading (`IX_BD_TIER1`) -/
  ty : Option KExpr := none

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
  /-- whether share sites under the same context reuse one walk (`IX_BD_NOMEMO`
  turns it off, for diagnosis) -/
  memo : Bool := true
  /-- whether the syntactic reading is measured beside the walk (`IX_BD_TIER1`) -/
  tier1 : Bool := false

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
  memo : Std.HashMap (Nat × Bool × List Nat × Option PropWhen × KExpr)
    (KExpr × Nat × Bool × KExpr) := {}
  /-- the stored walk's memo (`walkStored`): the variant of a share site -/
  memoS : Std.HashMap (Nat × Bool × List Nat) Nat := {}
  /-- the syntactic reading's binder counts (`IX_BD_TIER1`): agreeing with the walk's datum,
  disagreeing, not read where the walk decides, read where the walk does not, neither -/
  t1 : Array Nat := #[0, 0, 0, 0, 0]
  t1First : Option String := none

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

/-! ### Diagnosis (`IX_BD_TRACE`) -/

/-- A term for a trace line (keys as names, a bounded print). -/
def showTerm (e : KExpr) : String :=
  (Ix.KernelDisplay.renderTerm ({ maxSteps := 300 } : Ix.KernelDisplay.Cx .source) e).replace "\n" " "

private def nodeTag : KExpr → String
  | .bvar _ => "bvar" | .fvar .. => "fvar" | .app .. => "app" | .lam .. => "lam"
  | .forallE .. => "forall" | .letE .. => "let" | .proj .. => "proj" | .sort _ => "sort"
  | .const .. => "const" | .lit _ => "lit"

/-- The first place two terms differ (a trace's comparison of two sources), to
depth `fuel`. -/
def firstDiff : Nat → KExpr → KExpr → Option String
  | 0, _, _ => some "(the comparison's depth bound)"
  | fuel + 1, a, b =>
    if a == b then none else
    match a, b with
    | .app f x, .app g y => (firstDiff fuel f g).orElse fun _ => firstDiff fuel x y
    | .lam t c _, .lam u d _ | .forallE t c _, .forallE u d _ =>
      (firstDiff fuel t u).orElse fun _ => firstDiff fuel c d
    | .letE t v c _, .letE u w d _ =>
      ((firstDiff fuel t u).orElse fun _ => firstDiff fuel v w).orElse fun _ => firstDiff fuel c d
    | .proj k i x, .proj l j y =>
      if k == l && i == j then firstDiff fuel x y else some s!"proj {k}.{i} against {l}.{j}"
    | .const k us, .const l vs => some s!"const {k} {repr us} against {l} {repr vs}"
    | .sort u, .sort v => some s!"sort {repr u} against {repr v}"
    | .fvar i _, .fvar j _ => some s!"fvar {i} against {j}"
    | .bvar i, .bvar j => some s!"bvar {i} against {j}"
    | _, _ => some s!"{nodeTag a} against {nodeTag b}"

private def infers (cx : Cx) (depth : Nat) (e : KExpr) : CM Bool :=
  tryCatch (do let _ ← cx.core.infer depth e; pure true) (fun _ => pure false)

/-- Where `e`'s inference fails at `depth`, for a trace: the innermost failing
node found by descending (an application's first mismatching argument, a
projection's subject and table, a binder's domain or body). -/
def explain : Nat → Cx → Nat → KExpr → CM String
  | 0, _, _, _ => pure "(the descent's bound)"
  | fuel + 1, cx, depth, e => do
    if ← infers cx depth e then return "infers"
    match e with
    | .app .. =>
      let h := e.getAppFn
      unless ← infers cx depth h do return s!"head {showTerm h}: " ++ (← explain fuel cx depth h)
      let mut ty ← cx.core.infer depth h
      let mut i := 0
      for a in e.getAppArgsC do
        let w ← cx.core.whnf depth ty
        match w with
        | .forallE dom body _ =>
          unless ← infers cx depth a do
            return s!"argument {i} of {showTerm h}: " ++ (← explain fuel cx depth a)
          let ta ← cx.core.infer depth a
          unless ← cx.core.defeq depth ta dom do
            let wa ← cx.core.whnf depth ta
            let wd ← cx.core.whnf depth dom
            return s!"argument {i} of {showTerm h} mismatches: {showTerm a} : {showTerm ta} \
              (whnf {showTerm wa}), expected {showTerm dom} (whnf {showTerm wd}); \
              first difference of the whnfs: {(firstDiff 4096 wa wd).getD "none"}"
          ty := body.instantiate1C a
        | _ => return s!"argument {i} of {showTerm h}: a function was expected, its type is {showTerm w}"
        i := i + 1
      return s!"the spine of {showTerm h} checks, but the application does not infer"
    | .proj k i v =>
      unless ← infers cx depth v do return s!"the subject of {k}.{i}: " ++ (← explain fuel cx depth v)
      let tv ← cx.core.infer depth v
      let w ← cx.core.whnf depth tv
      match w.getAppFn with
      | .const T us =>
        match cx.fe.findProj? T i with
        | some en =>
          return s!"the projection {k}.{i}: its subject's type is headed by {T} (the same: {T == k}), \
            {w.getAppArgsC.length} arguments (table {en.numParams}), {us.length} levels \
            (table {en.levelParams.length}); the subject {showTerm v} : {showTerm w}"
        | none => return s!"the projection {k}.{i}: no table for {T}; the subject's type {showTerm w}"
      | _ => return s!"the projection {k}.{i}: the subject's type {showTerm w} is not a constant's"
    | .lam ty b _ | .forallE ty b _ =>
      unless ← infers cx depth ty do return "a binder's domain: " ++ (← explain fuel cx depth ty)
      return "under a binder: " ++ (← explain fuel cx (depth + 1) (b.instantiate1C (.fvar depth ty)))
    | _ => return s!"the leaf {showTerm e} ({nodeTag e})"

/-- IxC's datum of a run whose annotated opened leaf is `leaf` at `depth`
(`annotPwPiI` for a ∀ run, `annotPwLamI` for a λ run); `none` where IxC's
function fails. -/
def datum (cx : Cx) (pi : Bool) (depth : Nat) (leaf : KExpr) : EM (Option PropWhen) := do
  let act : CM PropWhen :=
    if pi then Ix.Kernel.Cached.annotPwPiI cx.core cx.fe depth leaf
    else Ix.Kernel.Cached.annotPwLamI cx.core cx.fe depth leaf
  let res : Option PropWhen ← (tryCatch (some <$> act) (fun e => do
      if cx.trace then
        let why ← (tryCatch (explain 64 cx depth leaf) (fun e => pure s!"(explain fails: {traceError e})") : CM String)
        dbgTrace s!"binder data trace: the datum of a {if pi then "∀" else "λ"} run at depth {depth} \
          fails: {traceError e}; {why}" fun _ => pure none
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

/-- What the walk knows of the type `T` of the term it walks: the zero-ness of
`T`'s sort (`pw`), the datum of a λ-run at `T` where IxC's datum function
fails. A λ's codomain sort has the zero-ness of the sort of the λ's own type
(the zero-ness of `imax u v` is that of `v`), so `pw` is the datum of every λ
of a run at `T`, and it passes unchanged to the run's body, to a `let`'s body
and into a share. A theorem's value has `pw = always`; a `let`'s value has its
declared type's. -/
structure Expect where
  pw : Option PropWhen := none
  /-- `pw` as the syntactic reading finds it (`synSort`; measurement only) -/
  syn : Option PropWhen := none
  deriving Inhabited

/-- The zero-ness of the sort of `t`, an annotated type at `depth` (IxC's
`annotPwPiI`); `none` where IxC's function fails. -/
def sortPwC (cx : Cx) (depth : Nat) (t : KExpr) : CM (Option PropWhen) :=
  tryCatch (some <$> Ix.Kernel.Cached.annotPwPiI cx.core cx.fe depth t) (fun _ => pure none)

/-! ### A syntactic reading of the data (measurement, `IX_BD_TIER1`)

Nothing below decides a datum the annotator writes: the walk counts where this
reading agrees with the datum it decided. -/

/-- `t` past exactly `n` leading ∀s. -/
def peelN : Nat → KExpr → Option KExpr
  | 0, t => some t
  | n + 1, .forallE _ b _ => peelN n b
  | _, _ => none

/-- The `n`-th ∀-domain of `t`, with the domains before it (innermost first). -/
def domainAt : Nat → KExpr → List (Option KExpr) → Option (KExpr × List (Option KExpr))
  | 0, .forallE d _ _, acc => some (d, acc)
  | n + 1, .forallE d b _, acc => domainAt n b (some d :: acc)
  | _, _, _ => none

/-- **The zero-ness of the sort of a type `t`, read syntactically**: its ∀-leaf is
a sort, or an application headed by a constant or a variable whose type, past
exactly the argument count of ∀s, is a sort. `ctx` holds the types of `t`'s loose
variables, innermost first; `sub` maps the levels found to the reader's
numbering. `none` where the reading does not apply (no whnf, no inference). -/
def synSort (fe : FEnv .source) (sub : Ix.Kernel.Level → Ix.Kernel.Level) :
    Nat → List (Option KExpr) → KExpr → Option PropWhen
  | 0, _, _ => none
  | fuel + 1, ctx, t =>
    match t with
    | .sort _ => some .never
    | .forallE dom body _ => synSort fe sub fuel (some dom :: ctx) body
    | _ =>
      let n := t.getAppArgsC.length
      let res : Option Ix.Kernel.Level := match t.getAppFn with
        | .const c us => (fe.find? c).bind fun ci =>
          match peelN n ci.toConstantVal.type with
          | some (.sort s) => some (Ix.Kernel.Level.subst ci.toConstantVal.levelParams us s)
          | _ => none
        | .bvar i => (ctx[i]?).join.bind fun ty => match peelN n ty with
          | some (.sort s) => some s
          | _ => none
        | .fvar _ ty => match peelN n ty with
          | some (.sort s) => some s
          | _ => none
        | _ => none
      res.map fun s => Ix.Kernel.Level.zeronessOf (sub s)

/-- The syntactic expectation of the argument at `idx` of a spine headed by `h`
(a source head under `ctx`): the zero-ness of the sort of the head type's
`idx`-th domain. -/
def synArg (fe : FEnv .source) (ctx : List CtxEntry) (h : KExpr) (idx : Nat) : Option PropWhen :=
  match h with
  | .const c us => (fe.find? c).bind fun ci =>
    (domainAt idx ci.toConstantVal.type []).bind fun (d, before) =>
      synSort fe (Ix.Kernel.Level.subst ci.toConstantVal.levelParams us) 64 before d
  | .bvar i => (ctx[i]?.bind (·.ty)).bind fun ty =>
    (domainAt idx ty []).bind fun (d, before) => synSort fe id 64 before d
  | _ => none

/-- Count `k` binders whose walked node is `node` against the syntactic reading
`syn` (`WState.t1`). -/
def countT1 (cx : Cx) (pi : Bool) (depth k : Nat) (node : Node) (syn : Option PropWhen) :
    WM Unit := do
  if !cx.tier1 then return
  let slot := match node, syn with
    | .undecided, some _ => 3
    | .undecided, none => 4
    | _, none => 2
    | _, some p => if cx.nodeOf p == node then 0 else 1
  modify fun st =>
    let first := if slot == 1 && st.t1First.isNone then
        some s!"{if pi then "∀" else "λ"} run at depth {depth}: read {repr syn}, walked {repr node}"
      else st.t1First
    { st with t1 := st.t1.modify slot (· + k), t1First := first }

/-- The walk of one entry's tree `e` beside its source `x`, under `ctx`
(innermost first) at binder depth `depth`, knowing `ex` of its type: the
annotated opened term, and whether anything in it is undecided. Every numbered
node of `e` gets its datum at its ordinal. -/
def walk : Nat → Cx → List CtxEntry → Nat → Expect → Ixon.Expr → KExpr → EM (KExpr × Bool)
  | 0, _, _, _, _, _, _ => mismatch "the walk's depth bound"
  | fuel + 1, cx, ctx, depth, ex, e, x =>
    match e, x with
    | .var i, _ =>
      match ctx[i.toNat]? with
      | some c => pure (c.val, false)
      | none => mismatch "a loose variable"
    | .app f a, .app xf xa => do
      let (f', bf) ← walk fuel cx ctx depth {} f xf
      let aex : Expect := if cx.tier1 then { syn := synArg cx.fe ctx x.getAppFn xf.getAppArgsC.length } else {}
      let (a', ba) ← walk fuel cx ctx depth aex a xa
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
        let (t', bt) ← walk fuel cx inner (depth + j) {} t ty
        bad := bad || bt
        let id ← freshId
        inner := ⟨id, .fvar (depth + j) t', some t'⟩ :: inner
        stk := (t', mb) :: stk
      let k := bs.size
      let leafEx : Expect := { pw := if !pi then ex.pw else none,
                               syn := if !pi && cx.tier1 then ex.syn else none }
      let (leaf', bl) ← walk fuel cx inner (depth + k) leafEx leafE leafX
      let pw? ← datum cx pi (depth + k) leaf'
      let pw? := if pw?.isSome || pi then pw? else ex.pw
      let undecided := bad || bl || pw?.isNone
      let node : Node := if undecided then .undecided else cx.nodeOf (pw?.getD .never)
      for ord in ords do setNode ord node
      if cx.tier1 then
        let synD : Option PropWhen := if pi then
            synSort cx.fe id 64 ((bs.toList.map fun (_, ty, _) => some ty).reverse ++ ctx.map (·.ty)) leafX
          else ex.syn
        countT1 cx pi depth k node synD
      let mk : KExpr → KExpr → BinderMeta → KExpr :=
        if pi then fun ty b mb => .forallE ty b mb else fun ty b mb => .lam ty b mb
      let out ← (Ix.Kernel.Cached.annotateBindersOutI mk depth (some (pw?.getD .never)) stk (k - 1)
        (leaf'.abstractRangeC depth k) : CM KExpr)
      pure (out, undecided)
    | .letE _ t v b, .letE ty val body _ => do
      -- IxC annotates the type and the value, then the body with the value
      -- transparent (its ζ-reduct)
      let (t', bt) ← walk fuel cx ctx depth {} t ty
      let vex : Expect ← if !bt then do
          let p ← (sortPwC cx depth t' : CM (Option PropWhen))
          pure { pw := p, syn := if cx.tier1 then synSort cx.fe id 64 (ctx.map (·.ty)) ty else none }
        else pure { syn := if cx.tier1 then synSort cx.fe id 64 (ctx.map (·.ty)) ty else none }
      let (v', bv) ← walk fuel cx ctx depth vex v val
      let id ← freshId
      let (b', bb) ← walk fuel cx (⟨id, v', some t'⟩ :: ctx) depth ex b body
      pure (b', bt || bv || bb)
    | .prj _ _ v, .proj k i xv => do
      let (v', bv) ← walk fuel cx ctx depth {} v xv
      if cx.trace then
        let probe : CM String := do
          let tpe ← cx.core.infer depth v'
          let te ← cx.core.whnf depth tpe
          let head := match Ix.Kernel.Expr.getAppFn te with
            | .const T _ => s!"const {T} (table: {(cx.fe.findProj? T i).isSome})"
            | _ => "not a constant"
          pure s!"the projection {k}.{i}: its subject's type is headed by {head}"
        let msg ← (tryCatch probe (fun e => do
          let why ← (tryCatch (explain 64 cx depth v') (fun e => pure s!"(explain fails: {traceError e})") : CM String)
          pure s!"the projection {k}.{i}: {traceError e}; {why}") : CM String)
        dbgTrace s!"binder data trace: {msg.take 3000}" fun _ => pure ()
      pure (.proj k i v', bv)
    | .share n, _ => do
      let ord ← reserve
      let n := n.toNat
      let shareEx : Expect := { pw := ex.pw,
                                syn := if cx.tier1 then ex.syn else none }
      let key := (n, cx.large, (ctx.take (cx.bounds[n]?.getD 0)).map (·.id), shareEx.pw, x)
      let st0 ← getThe WState
      let hit? := if cx.memo then st0.memo[key]? else none
      let (e', variant, bad) ← match hit? with
        | some (e', variant, bad, src) => do
          if cx.trace then
            if let some d := firstDiff 4096 src x then
              dbgTrace s!"binder data trace: share {n}: a memoized site's source differs: {d}"
                fun _ => pure ()
          pure (e', variant, bad)
        | none => do
          let some entry := cx.sharing[n]? | mismatch "a share"
          let ((e', bad), nodes) ← ((walk fuel cx ctx depth shareEx entry x).run #[] :
            WM ((KExpr × Bool) × Array Node))
          let variant ← variantOf n nodes
          modifyThe WState fun st => { st with memo := st.memo.insert key (e', variant, bad, x) }
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
    | _, _ =>
      let tag (e : Ixon.Expr) : String := match e with
        | .var _ => "var" | .app .. => "app" | .lam .. => "lam" | .all .. => "all"
        | .letE .. => "let" | .prj .. => "prj" | .share _ => "share" | .sort _ => "sort"
        | .ref .. => "ref" | .recur .. => "recur" | .str _ => "str" | .nat _ => "nat"
      let ktag : String := match k with
        | .bvar _ => "bvar" | .fvar .. => "fvar" | .app .. => "app" | .lam .. => "lam"
        | .forallE .. => "forall" | .letE .. => "let" | .proj .. => "proj" | .sort _ => "sort"
        | .const .. => "const" | .lit _ => "lit"
      mismatch s!"a node of the stored term (record {tag e}, stored {ktag})"

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

/-- For each root of `c` (`IxVM.PwHints.roots`' order), whether it is a
theorem's value. -/
def thmValues (c : Ixon.Constant) : Array Bool :=
  let ofDefn (d : Ixon.Definition) : Array Bool :=
    #[false, match d.kind with | .thm => true | _ => false]
  let ofMember : Ixon.MutConst → Array Bool
    | .defn d => ofDefn d
    | .indc i => Array.replicate (1 + i.ctors.size) false
    | .recr r => Array.replicate (1 + r.rules.size) false
  match c.info with
  | .defn d => ofDefn d
  | .axio _ | .quot _ => #[false]
  | .recr r => Array.replicate (1 + r.rules.size) false
  | .muts ms => ms.foldl (init := #[]) fun acc m => acc ++ ofMember m
  | _ => #[]

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
  -- each root's levels in the compiler's canonical form, as the install's
  -- declarations carry them (`Ix.LeanIngress.canonDecl`), over its constant's own
  -- level parameters
  return (roots.zip (items.map (·.1))).map fun (x, σ) => ((canonExprM σ.params x).run' {}, σ)

/-! ## The annotator -/

/-- **The section of a block record**, from its members' sources: IxC's pass
over each root beside its source, against the installed environment. -/
def annotateWalk (k : Installed) (extra : Array (Ix.Name × Ix.ConstantInfo)) (names : Array Ix.Name)
    (c : Ixon.Constant) : Array Ixon.BinderBlock :=
  let rs := IxVM.PwHints.roots c
  if rs.isEmpty then #[] else
  if unsafeOrPartial c then Ix.CompileM.undecidedSection c else
  match sourceRoots k.env extra names c with
  | none => Ix.CompileM.undecidedSection c
  | some xs =>
    let traced := !k.trace.isEmpty && names.any fun n => k.trace.contains n.pretty
    let cx0 : Cx := { fe := k.fe, core := k.core, sharing := c.sharing,
                      bounds := IxVM.PwHints.bounds c.sharing, trace := traced, memo := k.memo,
                      tier1 := k.tier1 }
    let stored : Array (Option KExpr) := if !k.stored then #[] else
      ((members c).zip names).foldl (fun acc (m, n) => acc ++ storedItems k.fe n m) #[]
    let tys := IxVM.PwHints.valueTypes c
    let thms := thmValues c
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
              (fun e => if cx.trace then
                  dbgTrace s!"binder data trace: root {i}: the stored walk fails: {traceError e}"
                    fun _ => pure none
                else pure none)
          | _ => pure none
        let ex : Expect ← match tys[i]? with
          | some (some j) => do
            -- the syntactic reading's expectation (measurement only)
            let syn : Option PropWhen := if !cx.tier1 then none
              else if thms[i]?.getD false then some (PropWhen.ifAllZero [])
              else (xs[j]?).bind fun (tx, _) => synSort cx.fe id 64 [] tx
            if thms[i]?.getD false then pure { pw := some (PropWhen.ifAllZero []), syn }
            else match annotated[j]?.join with
              | some t => do
                let p ← (sortPwC cx 0 t : CM (Option PropWhen))
                pure { pw := p, syn }
              | none => pure { syn }
          | _ => pure {}
        let (nodes, kx?) ← match read, stored[i]? with
          | some nodes, some kx => pure (nodes, kx)
          | _, _ => do
            let ((kx, bad), nodes) ← (walk walkFuel cx [] 0 ex rs[i] x).run #[]
            pure (nodes, if bad then none else some kx)
        annotated := annotated.push kx?
        out := out.push ⟨0, i, 0, nodes⟩
      return out
    match (act.run {}).run {} with
    | .ok ((roots, st), _) =>
      let sec := match Ix.Compile.BinderData.sectionOf c (roots ++ st.blocks) with
        | .ok s => s
        | .error _ => Ix.CompileM.undecidedSection c
      if k.tier1 then
        let counts := String.intercalate " " (st.t1.toList.map toString)
        let name := (names[0]?.map (·.pretty)).getD "?"
        let first := st.t1First.getD ""
        dbgTrace s!"BDT1 {counts} {name} {first}" fun _ => sec
      else sec
    | .error e =>
      if traced then
        dbgTrace s!"binder data trace: {names.map (·.pretty)}: the walk fails: {traceError e}"
          fun _ => Ix.CompileM.undecidedSection c
      else Ix.CompileM.undecidedSection c

/-- **The section of a block record**: read off its members' sources where every
binder shows its datum (`Ix.Compile.BinderRead`), else IxC's pass over each root
beside its source (`annotateWalk`). -/
def annotate (k : Installed) (extra : Array (Ix.Name × Ix.ConstantInfo)) (names : Array Ix.Name)
    (c : Ixon.Constant) : Array Ixon.BinderBlock :=
  if (IxVM.PwHints.roots c).isEmpty then #[] else
  if unsafeOrPartial c then Ix.CompileM.undecidedSection c else
  let find : Ix.Compile.BinderRead.Find := fun n =>
    ((extra.find? (·.1 == n)).map (·.2)).orElse fun _ => k.env.consts.get? n
  let stat (route why : String) (s : Array Ixon.BinderBlock) : Array Ixon.BinderBlock :=
    if k.t1stat then
      let name := (names[0]?.map (·.pretty)).getD "?"
      dbgTrace s!"BDT1R {route} {name} {why}" fun _ => s
    else s
  let read : Except String (Array Ixon.BinderBlock) :=
    if k.noread then .error "the reading is off" else Ix.Compile.BinderRead.sectionWhy find names c
  match read with
  | .ok s => stat "read" "" s
  | .error why =>
    stat "walk" why (if k.readonly then Ix.CompileM.undecidedSection c else annotateWalk k extra names c)

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
