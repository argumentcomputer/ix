/-
  canon-census: the canonicalisation census of a library, computed by Pass 1
  (`Ix.Compile.Canon`) under `Rules.today` and `Rules.phaseA`.

  ```
  canon-census <source.lean> <stored.ixe> [--tsv <blocks.tsv>]
  ```

  * `<source.lean>` is elaborated like `ix compile <source.lean> --no-build`
    (`Ix.Meta.getFileEnvCore`; the imports must be built): Init+Std through
    `Benchmarks/Compile/CompileInitStd.lean`, Mathlib through
    `Benchmarks/Compile/CompileMathlib.lean` (the `Benchmarks/Compile` Lake
    project, whose `.lake` must be present);
  * `<stored.ixe>` supplies the compiled address of every named constant
    (its side-car, read metadata-light by `Ixon.rsDeEnvLazyFFI`), which the
    comparator uses for external references;
  * `--tsv` writes one row per Lean block (both rule sets' classes,
    permutations and change flags) for cross-checking.

  Printed: the headline table of `exp-census-1.md` (constants; Lean
  inductive blocks by `InductiveVal.all`, of which mutual / nested / Prop /
  unsafe / reflexive; blocks changed and by which operation; orders decided
  by addresses), one line per changed block, the comparator study, the
  discovery-order validation against Lean's `rec_N`, and the clique census.

  Untrusted measurement tooling; it never writes an environment.
-/
import Ix.Meta
import Ix.CanonM
import Ix.Ixon
import Ix.Compile.Canon
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Elab.PreDefinition.PartialFixpoint.Eqns

open Ix.Compile.Canon

namespace Benchmarks.Canon.Census

/-! ## Reading the Lean side -/

/-- `Sort 0` at the end of a type's `∀` telescope. -/
partial def resultIsProp : Lean.Expr → Bool
  | .forallE _ _ b _ => resultIsProp b
  | .mdata _ e => resultIsProp e
  | .sort .zero => true
  | _ => false

/-- Convert a list of Lean constants in parallel chunks. -/
def canonConsts (cs : Array (Lean.Name × Lean.ConstantInfo)) (workers : Nat := 32) :
    Std.HashMap Ix.Name Ix.ConstantInfo := Id.run do
  let size := (cs.size + workers - 1) / workers
  let chunks := Ix.CanonM.chunks cs (max size 1)
  let tasks := chunks.map fun ch => Task.spawn fun _ => Ix.CanonM.canonChunk ch
  let mut m : Std.HashMap Ix.Name Ix.ConstantInfo := {}
  for t in tasks do
    for (n, c) in t.get do
      m := m.insert n c
  return m

/-- Every entry of a `MapDeclarationExtension` from every imported module,
at both export levels. -/
def mapExtEntries {α : Type} [Inhabited α] (ext : Lean.MapDeclarationExtension α)
    (env : Lean.Environment) : Array (Lean.Name × α) := Id.run do
  let mut seen : Lean.NameSet := {}
  let mut out : Array (Lean.Name × α) := #[]
  for i in [0:env.allImportedModuleNames.size] do
    for level in [Lean.OLeanLevel.exported, .private] do
      for (n, a) in ext.toPersistentEnvExtension.getModuleEntries env i (level := level) do
        if !seen.contains n then
          seen := seen.insert n
          out := out.push (n, a)
  for (n, a) in (ext.getState env).toList do
    if !seen.contains n then
      seen := seen.insert n
      out := out.push (n, a)
  return out

/-- A clique as read from Lean, before conversion. -/
structure RawMember where
  name : Lean.Name
  levelParams : List Lean.Name
  type : Lean.Expr
  value : Lean.Expr
  recArgPos : Option Nat := none

structure RawClique where
  kind : CliqueKind
  members : Array RawMember

def convertClique (rc : RawClique) : Ix.CanonM.CanonM Clique := do
  let ms ← rc.members.mapM fun m => do
    let name ← Ix.CanonM.canonName m.name
    let lps ← m.levelParams.toArray.mapM Ix.CanonM.canonName
    let type ← Ix.CanonM.canonExpr m.type
    let value ← Ix.CanonM.canonExpr m.value
    pure { name, levelParams := lps, type, value, recArgPos := m.recArgPos : CliqueMember }
  return { kind := rc.kind, members := ms }

/-- The cliques of a Lean environment (M.1). Multi-member cliques carry
their specifications; `counts` counts every clique (singletons included). -/
def readCliques (env : Lean.Environment) :
    Array RawClique × Std.HashMap String (Nat × Nat) := Id.run do
  let mut counts : Std.HashMap String (Nat × Nat) := {}
  let bump := fun (m : Std.HashMap String (Nat × Nat)) (k : CliqueKind) (size : Nat) =>
    let (a, b) := m.getD k.name (0, 0)
    m.insert k.name (a + 1, if size ≥ 2 then b + 1 else b)
  let mut out : Array RawClique := #[]
  let mut inEqn : Lean.NameSet := {}
  -- structural
  let st := mapExtEntries Lean.Elab.Structural.eqnInfoExt env
  let stMap : Std.HashMap Lean.Name Lean.Elab.Structural.EqnInfo := st.foldl (init := {})
    fun m (n, i) => m.insert n i
  let mut done : Lean.NameSet := {}
  for (_, i) in st do
    let some first := i.declNames[0]? | continue
    if done.contains first then continue
    done := done.insert first
    for n in i.declNames do inEqn := inEqn.insert n
    counts := bump counts .structural i.declNames.size
    if i.declNames.size ≥ 2 then
      let ms := i.declNames.filterMap fun n => (stMap.get? n).map fun j =>
        { name := n, levelParams := j.levelParams, type := j.type, value := j.value,
          recArgPos := some j.recArgPos : RawMember }
      if ms.size == i.declNames.size then out := out.push { kind := .structural, members := ms }
  -- well-founded
  let wf := mapExtEntries Lean.Elab.WF.eqnInfoExt env
  let wfMap : Std.HashMap Lean.Name Lean.Elab.WF.EqnInfo := wf.foldl (init := {})
    fun m (n, i) => m.insert n i
  done := {}
  for (_, i) in wf do
    let some first := i.declNames[0]? | continue
    if done.contains first then continue
    done := done.insert first
    for n in i.declNames do inEqn := inEqn.insert n
    counts := bump counts .wellFounded i.declNames.size
    if i.declNames.size ≥ 2 then
      let ms := i.declNames.filterMap fun n => (wfMap.get? n).map fun j =>
        { name := n, levelParams := j.levelParams, type := j.type, value := j.value : RawMember }
      if ms.size == i.declNames.size then out := out.push { kind := .wellFounded, members := ms }
  -- partial_fixpoint
  let pf := mapExtEntries Lean.Elab.PartialFixpoint.eqnInfoExt env
  let pfMap : Std.HashMap Lean.Name Lean.Elab.PartialFixpoint.EqnInfo := pf.foldl (init := {})
    fun m (n, i) => m.insert n i
  done := {}
  for (_, i) in pf do
    let some first := i.declNames[0]? | continue
    if done.contains first then continue
    done := done.insert first
    for n in i.declNames do inEqn := inEqn.insert n
    counts := bump counts .partialFixpoint i.declNames.size
    if i.declNames.size ≥ 2 then
      let ms := i.declNames.filterMap fun n => (pfMap.get? n).map fun j =>
        { name := n, levelParams := j.levelParams, type := j.type, value := j.value : RawMember }
      if ms.size == i.declNames.size then out := out.push { kind := .partialFixpoint, members := ms }
  -- partial, unsafe, no specification: by `all`
  done := {}
  for (n, c) in env.constants.toList do
    match n with
    | .str _ "_unsafe_rec" => continue
    | _ => pure ()
    if inEqn.contains n then continue
    let all := c.all
    let some first := all.head? | continue
    let kind? : Option CliqueKind := match c with
      | .opaqueInfo _ =>
        if env.contains (Lean.Name.str n "_unsafe_rec") then some .partial else none
      | .defnInfo v =>
        if v.safety == .unsafe then
          if all.length ≥ 2 || v.value.getUsedConstants.contains n then some .unsafe else none
        else if all.length ≥ 2 then some .noSpec else none
      | .thmInfo _ => if all.length ≥ 2 then some .noSpec else none
      | _ => none
    let some kind := kind? | continue
    if done.contains first then continue
    done := done.insert first
    counts := bump counts kind all.length
    if all.length ≥ 2 && kind != .noSpec then
      let ms := all.toArray.filterMap fun m =>
        match kind, env.find? m, env.find? (Lean.Name.str m "_unsafe_rec") with
        | .partial, some ci, some (.defnInfo u) =>
          some { name := m, levelParams := ci.levelParams, type := ci.type,
                 value := u.value.replace fun e => match e with
                   | .const (.str b "_unsafe_rec") ls =>
                     if all.contains b then some (.const b ls) else none
                   | _ => none : RawMember }
        | .unsafe, some (.defnInfo d), _ =>
          some { name := m, levelParams := d.levelParams, type := d.type, value := d.value }
        | _, _, _ => none
      if ms.size == all.length then out := out.push { kind, members := ms }
  return (out, counts)

/-! ## Report -/

structure Counts where
  changed : Nat := 0
  reorder : Nat := 0
  split : Nat := 0
  splitCross : Nat := 0
  collapse : Nat := 0
  nestedOrder : Nat := 0
  nestedOnly : Nat := 0
  reorderOnly : Nat := 0
  reorderAndNested : Nat := 0
  evaporation : Nat := 0
  propGainCandidates : Nat := 0
  multiClass : Nat := 0
  memberAddr : Nat := 0
  multiAux : Nat := 0
  nestedAddr : Nat := 0
  hazards : Nat := 0
  addrTieBreaks : Nat := 0
  preorderBlocks : Nat := 0
  preorderViolations : Nat := 0
  errors : Nat := 0
  lines : Array String := #[]
  errorLines : Array String := #[]
  violationLines : Array String := #[]

def ops (c : BlockChange) (cross : Bool) : String :=
  let xs := (if c.reorder then ["member reorder"] else []) ++
    (if c.split then [if cross then "split with cross fields" else "split"] else []) ++
    (if c.collapse then ["collapse"] else []) ++
    (if c.nestedOrder then ["nested-auxiliary order"] else []) ++
    (if c.evaporation then ["evaporation"] else [])
  ", ".intercalate xs

/-- Some constructor of a component references a member of another. -/
def crossFields (env : Env) (b : BlockCanon) : Bool :=
  b.components.size > 1 && b.components.zipIdx.any fun (c, i) =>
    c.members.any fun m => match env.const? m with
      | some (.inductInfo v) => v.ctors.any fun cn => match env.const? cn with
        | some ctor => (refsConst ctor).toList.any fun r =>
            b.components.zipIdx.any fun (d, j) => j != i && d.members.contains r
        | none => false
      | _ => false

/-- A split component with a single Prop member of at most one constructor
whose Lean recursor eliminates only into Prop: it may gain large
elimination (an upper bound; deciding it needs the kernel's field check). -/
def propGainCandidate (env : Env) (isProp : Ix.Name → Bool) (b : BlockCanon) : Bool :=
  b.components.size > 1 && b.components.any fun c =>
    c.members.size == 1 && c.members.all fun m =>
      isProp m && match env.const? m, env.const? (Ix.Name.mkStr m "rec") with
        | some (.inductInfo v), some (.recInfo r) =>
          v.ctors.size ≤ 1 && r.cnst.levelParams.size == v.cnst.levelParams.size
        | _, _ => false

def record (rules : Rules) (env : Env) (isProp : Ix.Name → Bool) (all : Array Ix.Name)
    (b : BlockCanon) (c : Counts) : Counts := Id.run do
  let ch := b.change
  let mut c := c
  let cross := crossFields env b
  if b.multiClass then c := { c with multiClass := c.multiClass + 1 }
  if b.memberOrderAddrDecided then c := { c with memberAddr := c.memberAddr + 1 }
  if b.multiAux then c := { c with multiAux := c.multiAux + 1 }
  if b.nestedOrderAddrDecided then c := { c with nestedAddr := c.nestedAddr + 1 }
  if propGainCandidate env isProp b then c := { c with propGainCandidates := c.propGainCandidates + 1 }
  for comp in b.components do
    c := { c with hazards := c.hazards + comp.stats.hazards,
                  addrTieBreaks := c.addrTieBreaks + comp.stats.addrDecided }
  if !ch.any then return c
  c := { c with changed := c.changed + 1 }
  if ch.reorder then c := { c with reorder := c.reorder + 1 }
  if ch.split then c := { c with split := c.split + 1 }
  if ch.split && cross then c := { c with splitCross := c.splitCross + 1 }
  if ch.collapse then c := { c with collapse := c.collapse + 1 }
  if ch.nestedOrder then c := { c with nestedOrder := c.nestedOrder + 1 }
  if ch.evaporation then c := { c with evaporation := c.evaporation + 1 }
  let other := ch.split || ch.collapse || ch.evaporation
  if ch.nestedOrder && !ch.reorder && !other then c := { c with nestedOnly := c.nestedOnly + 1 }
  if ch.reorder && !ch.nestedOrder && !other then c := { c with reorderOnly := c.reorderOnly + 1 }
  if ch.reorder && ch.nestedOrder && !other then
    c := { c with reorderAndNested := c.reorderAndNested + 1 }
  let addr := (if b.memberOrderAddrDecided then " [member order by address]" else "") ++
    (if b.nestedOrderAddrDecided then " [nested order by address]" else "")
  let perms := b.components.filterMap fun comp => comp.nested.map fun n =>
    n.perm.map fun p => match p with
      | some i => toString i
      | none => "out"
  let classesStr := toString (b.components.map fun comp => comp.classes.map (·.map namePretty))
  let permStr := if perms.isEmpty then "" else "; perm " ++ toString perms
  let line := s!"{rules.name}: {namePretty all[0]!} ({all.size} members): {ops ch cross}{addr}; classes {classesStr}{permStr}"
  c := { c with lines := c.lines.push line }
  return c

def pct (a b : Nat) : String := s!"{a} of {b}"

def main (args : List String) : IO UInt32 := do
  let (src, ixe, tsv?) ← match args with
    | [s, i] => pure (s, i, none)
    | [s, i, "--tsv", t] => pure (s, i, some t)
    | _ =>
      IO.eprintln "usage: canon-census <source.lean> <stored.ixe> [--tsv <blocks.tsv>]"
      return 2
  let t0 ← IO.monoMsNow
  let fe ← getFileEnvCore src
  let leanEnv := fe.env
  let nLean := leanEnv.constants.fold (fun n _ _ => n + 1) 0
  IO.eprintln s!"[census] {src}: {nLean} Lean constants ({(← IO.monoMsNow) - t0} ms)"
  let bytes ← IO.FS.readBinFile ixe
  let raw ← IO.ofExcept (Ixon.rsDeEnvLazyFFI bytes)
  let addrs : Std.HashMap Ix.Name Address := raw.named.foldl (init := {}) fun m n => m.insert n.name n.addr
  IO.eprintln s!"[census] {ixe}: {raw.named.size} named, {raw.consts.size} constants"

  -- inductive data, converted to Ix
  let indLike := leanEnv.constants.toList.toArray.filter fun (_, c) =>
    match c with
    | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
    | _ => false
  let consts := canonConsts indLike
  IO.eprintln s!"[census] {consts.size} inductive-family constants converted ({(← IO.monoMsNow) - t0} ms)"
  let env : Env := { const? := consts.get?, addr? := addrs.get? }
  let isPropL : Std.HashSet Ix.Name := indLike.foldl (init := {}) fun s (n, c) =>
    match c with
    | .inductInfo v => if resultIsProp v.type then s.insert (Ix.Name.fromLeanName n) else s
    | _ => s
  let isProp := fun n => isPropL.contains n

  -- blocks
  let mut blocks : Array (Array Ix.Name) := #[]
  let mut seen : Std.HashSet Ix.Name := {}
  for (_, c) in consts do
    if let .inductInfo v := c then
      if let some a0 := v.all[0]? then
        if !seen.contains a0 then
          seen := seen.insert a0
          blocks := blocks.push v.all
  blocks := blocks.qsort fun a b => namePretty a[0]! < namePretty b[0]!
  let member := fun (n : Ix.Name) => match consts.get? n with
    | some (.inductInfo v) => some v
    | _ => none
  let nMutual := blocks.filter (·.size > 1) |>.size
  let nNested := blocks.filter (·.any fun n => match member n with
    | some v => decide (v.numNested > 0)
    | none => false) |>.size
  let nProp := blocks.filter (·.any isProp) |>.size
  let nUnsafe := blocks.filter (·.any fun n => ((member n).map (·.isUnsafe)).getD false) |>.size
  let nRefl := blocks.filter (·.any fun n => ((member n).map (·.isReflexive)).getD false) |>.size
  let nGenerated := blocks.filter (·.any fun n => match n with
    | .str _ s _ => s == "below" || s.startsWith "below_"
    | _ => false) |>.size

  let mut today : Counts := {}
  let mut phaseA : Counts := {}
  let mut discChecked := 0
  let mut discMismatch : Array String := #[]
  let mut dedupDiffers : Array String := #[]
  let mut tsvRows : Array String := #["block\tmembers\trules\tchanged\tops\tclasses\tperm"]
  let mut movesK : Array String := #[]
  let mut movesU : Array String := #[]
  let mut movesA : Array String := #[]
  let mut swept := 0
  let mut sweepFail : Array String := #[]
  for all in blocks do
    -- order moves against today (member classes as sets, in order)
    let setsOf : Rules → Except String (Array (Array (Array Ix.Name))) := fun r => do
      let comps ← blockComponents env all
      comps.mapM fun (ms : Array Ix.Name) => do
        let cs ← ms.toList.mapM (mutConstOf env)
        let (cls, _) ← sortClasses r env.addr? cs
        pure (classSets cls)
    match setsOf Rules.today, setsOf Rules.todayK, setsOf Rules.todayU,
        setsOf { Rules.phaseA with seed := .byNameHash } with
    | .ok t, .ok k, .ok u, .ok a =>
      if t.any (·.size > 1) then
        if k != t then movesK := movesK.push s!"{namePretty all[0]!}: {k.map (·.map (·.map namePretty))} vs {t.map (·.map (·.map namePretty))}"
        if u != t then movesU := movesU.push s!"{namePretty all[0]!}: {u.map (·.map (·.map namePretty))} vs {t.map (·.map (·.map namePretty))}"
        if a != t then movesA := movesA.push s!"{namePretty all[0]!}"
    | _, _, _, _ => pure ()
    -- seed sweep
    if let .ok comps := blockComponents env all then
      for ms in comps do
        if ms.size ≥ 2 then
          if let .ok cs := ms.toList.mapM (mutConstOf env) then
            swept := swept + 1
            for r in [Rules.today, Rules.phaseA] do
              match seedSweep r env.addr? cs with
              | .ok none => pure ()
              | .ok (some d) => sweepFail := sweepFail.push s!"{r.name} {namePretty all[0]!}: {d}"
              | .error e => sweepFail := sweepFail.push s!"{r.name} {namePretty all[0]!}: error {e}"
    for rules in [Rules.today, Rules.phaseA] do
      match canonBlock rules env all with
      | .error e =>
        let line := s!"{rules.name}: {namePretty all[0]!}: {e}"
        if rules == .today then today := { today with errors := today.errors + 1, errorLines := today.errorLines.push line }
        else phaseA := { phaseA with errors := phaseA.errors + 1, errorLines := phaseA.errorLines.push line }
      | .ok b =>
        let c0 := if rules == .today then today else phaseA
        let mut c := record rules env isProp all b c0
        -- comparator study
        for comp in b.components do
          if comp.members.size ≥ 2 && comp.members.size ≤ 40 then
            let cs := comp.classes.toList.map fun cls =>
              cls.toList.filterMap fun n => (mutConstOf env n).toOption
            c := { c with preorderBlocks := c.preorderBlocks + 1 }
            match preorderViolations rules env.addr? cs with
            | .ok vs =>
              if !vs.isEmpty then
                c := { c with preorderViolations := c.preorderViolations + 1,
                              violationLines := c.violationLines.push s!"{namePretty all[0]!}: {vs.toList.take 5}" }
            | .error e => c := { c with violationLines := c.violationLines.push s!"{namePretty all[0]!}: error {e}" }
        if rules == .today then today := c else phaseA := c
        let ch := b.change
        let perms := b.components.filterMap fun comp => comp.nested.map fun n =>
          ",".intercalate (n.perm.toList.map fun p => match p with | some i => toString i | none => "out")
        tsvRows := tsvRows.push s!"{namePretty all[0]!}\t{all.size}\t{rules.name}\t{ch.any}\t{ops ch false}\t\
          {b.components.map fun comp => comp.classes.map (·.map namePretty)}\t{perms}"
    -- discovery order against rec_N
    let some a0 := all[0]? | continue
    let some v := member a0 | continue
    if v.numNested > 0 then
      discChecked := discChecked + 1
      match expand env.ind? .lean all, expand env.ind? .compiler all with
      | .ok x, .ok y =>
        let sigs := x.sigs
        let recs := recMajorSignatures env.const? a0 v.numParams sigs.size
        let ok := sigs.size == v.numNested && (sigs.zip recs).all fun (s, r) =>
          match r with
          | some (h, ls, ps) => s.head == h && s.levels == ls && s.specs.size == ps.size &&
              (s.specs.zip ps).all fun (p, q) => auxSpecEq (fun _ => none) {} p q
          | none => false
        if !ok then discMismatch := discMismatch.push s!"{namePretty a0}: {sigs.size} vs numNested {v.numNested}"
        if y.sigs.size != sigs.size then
          dedupDiffers := dedupDiffers.push s!"{namePretty a0}: Lean {sigs.size}, compiler {y.sigs.size}"
      | .error e, _ | _, .error e => discMismatch := discMismatch.push s!"{namePretty a0}: {e}"
  IO.eprintln s!"[census] blocks done ({(← IO.monoMsNow) - t0} ms)"

  -- cliques
  let (rawCliques, cliqueCounts) := readCliques leanEnv
  let cliques : Array Clique := (rawCliques.mapM convertClique).run' {} |>.run
  let mut cliqueRows : Std.HashMap String (Nat × Nat × Nat × Nat × Nat) := {}
  let mut cliqueLines : Array String := #[]
  let mut cliqueMovesK := 0
  let mut cliqueMovesU := 0
  let mut cliqueSweepFail : Array String := #[]
  for cl in cliques do
    let cs := cl.members.toList.map (·.toMutConst)
    let setsOf := fun (r : Rules) => match sortClasses r env.addr? cs with
      | .ok (x, _) => Except.ok (classSets x)
      | .error e => Except.error e
    match setsOf Rules.today, setsOf Rules.todayK, setsOf Rules.todayU with
    | .ok t, .ok k, .ok u =>
      if k != t then cliqueMovesK := cliqueMovesK + 1
      if u != t then cliqueMovesU := cliqueMovesU + 1
    | _, _, _ => pure ()
    for r in [Rules.today, Rules.phaseA] do
      match seedSweep r env.addr? cs with
      | .ok none => pure ()
      | .ok (some d) => cliqueSweepFail := cliqueSweepFail.push s!"{r.name} {cl.names.map namePretty}: {d}"
      | .error e => cliqueSweepFail := cliqueSweepFail.push s!"{r.name}: error {e}"
    let several := cl.kind == .structural && severalPerTypeFormer cl
    let mut chT := false
    let mut chA := false
    for rules in [Rules.today, Rules.phaseA] do
      match cliqueClasses rules env.addr? cl with
      | .ok (cls, _) =>
        let ch := cliqueChanged cl cls
        if rules == .today then chT := ch else chA := ch
        if ch then
          cliqueLines := cliqueLines.push s!"{rules.name}: {cl.kind.name} {cl.names.map namePretty} → \
            {cls.map (·.map namePretty)}"
      | .error e => cliqueLines := cliqueLines.push s!"{rules.name}: {cl.kind.name} {cl.names.map namePretty}: error {e}"
    let (a, b, c, d, e) := cliqueRows.getD cl.kind.name (0, 0, 0, 0, 0)
    cliqueRows := cliqueRows.insert cl.kind.name
      (a + 1, if several then b + 1 else b, if chT then c + 1 else c, if chA then d + 1 else d, e)

  -- output
  let p := fun (s : String) => IO.println s
  p s!"# Canonicalisation census: {src}"
  p ""
  p s!"Lean constants: {nLean}; stored environment: {raw.named.size} named, \
    {raw.consts.size} constants."
  p ""
  p "| | today | phaseA |"
  p "|---|---|---|"
  p s!"| Lean inductive blocks (by `InductiveVal.all`) | {blocks.size} | {blocks.size} |"
  p s!"| – of which mutual | {nMutual} | {nMutual} |"
  p s!"| – nested / Prop / unsafe / reflexive | {nNested} / {nProp} / {nUnsafe} / {nRefl} | same |"
  p s!"| – Lean-generated (`below`, `below_N`) | {nGenerated} | same |"
  p s!"| **Blocks canonicalisation changes** | **{today.changed}** | **{phaseA.changed}** |"
  p s!"| – member reorder | {today.reorder} | {phaseA.reorder} |"
  p s!"| – split / split with cross fields | {today.split} / {today.splitCross} | {phaseA.split} / {phaseA.splitCross} |"
  p s!"| – collapse | {today.collapse} | {phaseA.collapse} |"
  p s!"| – nested-auxiliary order differs from Lean | {today.nestedOrder} | {phaseA.nestedOrder} |"
  p s!"| – of which nested order only / reorder only / both | {today.nestedOnly} / {today.reorderOnly} / {today.reorderAndNested} | {phaseA.nestedOnly} / {phaseA.reorderOnly} / {phaseA.reorderAndNested} |"
  p s!"| – evaporation | {today.evaporation} | {phaseA.evaporation} |"
  p s!"| – Prop member may gain large elimination (upper bound) | {today.propGainCandidates} | {phaseA.propGainCandidates} |"
  p s!"| Orders decided by addresses: member | {pct today.memberAddr today.multiClass} | {pct phaseA.memberAddr phaseA.multiClass} |"
  p s!"| Orders decided by addresses: nested auxiliaries | {pct today.nestedAddr today.multiAux} | n/a (discovery) |"
  p s!"| `byAddress` comparisons decided by address | – | {phaseA.addrTieBreaks} |"
  p s!"| Reversed non-equal cache hits (Lean/Rust divergence) | {today.hazards} | {phaseA.hazards} |"
  p s!"| Comparator: components checked / with violations | {today.preorderBlocks} / {today.preorderViolations} | {phaseA.preorderBlocks} / {phaseA.preorderViolations} |"
  p s!"| Errors | {today.errors} | {phaseA.errors} |"
  p ""
  p s!"Member order moves against today (blocks with several classes): under `(k₀, k₁)` alone {movesK.size}; \
    under levels after `canonUniv` alone {movesU.size}; under both {movesA.size}."
  for l in movesK do p s!"- (k0,k1) moves: {l}"
  for l in movesU do p s!"- canonUniv moves: {l}"
  p s!"Seed sweep (identity, reverse, name-hash, 10 random presentations; today's comparator with the port fixes, and phaseA): \
    {swept} components, {sweepFail.size} differences."
  for l in sweepFail.toList.take 30 do p s!"- seed sweep: {l}"
  p ""
  p s!"Discovery order vs Lean's `rec_N`: {discChecked} nested blocks checked, {discMismatch.size} mismatches; \
    compiler deduplication gives a different auxiliary count on {dedupDiffers.size}."
  for l in discMismatch.toList.take 30 do p s!"- rec_N mismatch: {l}"
  for l in dedupDiffers.toList.take 30 do p s!"- dedup: {l}"
  p ""
  p "## Changed blocks"
  for l in today.lines ++ phaseA.lines do p s!"- {l}"
  p ""
  if !(today.errorLines ++ phaseA.errorLines).isEmpty then
    p "## Errors"
    for l in (today.errorLines ++ phaseA.errorLines).toList.take 60 do p s!"- {l}"
    p ""
  if !(today.violationLines ++ phaseA.violationLines).isEmpty then
    p "## Comparator violations"
    for l in (today.violationLines ++ phaseA.violationLines).toList.take 60 do p s!"- {l}"
    p ""
  p "## Cliques"
  p ""
  p "| kind | cliques | with ≥ 2 members | ≥ 2 members, specified | several per type former | change order (today) | change order (phaseA) |"
  p "|---|---|---|---|---|---|---|"
  for k in [CliqueKind.structural, .wellFounded, .partialFixpoint, .noSpec, .partial, .unsafe] do
    let (n, m) := cliqueCounts.getD k.name (0, 0)
    let (s, sev, ct, ca, _) := cliqueRows.getD k.name (0, 0, 0, 0, 0)
    p s!"| {k.name} | {n} | {m} | {s} | {if k == .structural then toString sev else "n/a"} | {ct} | {ca} |"
  p ""
  p s!"Clique order moves against today: `(k₀, k₁)` alone {cliqueMovesK}, `canonUniv` alone {cliqueMovesU}; \
    seed sweep differences {cliqueSweepFail.size} (of {cliques.size} specified cliques)."
  for l in cliqueSweepFail.toList.take 20 do p s!"- clique seed sweep: {l}"
  p ""
  for l in cliqueLines do p s!"- {l}"
  if let some path := tsv? then
    IO.FS.writeFile path ("\n".intercalate tsvRows.toList ++ "\n")
  IO.eprintln s!"[census] done ({(← IO.monoMsNow) - t0} ms)"
  return 0

end Benchmarks.Canon.Census

def main (args : List String) : IO UInt32 := Benchmarks.Canon.Census.main args
