/-
  `ix validate-lean <file.lean>`: the validator of record for Phase A
  (design `docs/compiler-passes.md` §9). Pure Lean, over the Lean compiler's output
  (Pass 3, the only mode since M6R slice 6). With `--ixe` it reads any
  stored file, also one the legacy call-site surgery wrote before slice 6
  (no `_ix` names: its changed blocks are reported, not oracle subjects).

  Phases (each a function below with a paragraph saying what it
  establishes and what it does not; the old numbers are kept where their
  meaning survived):

    1. Compile                — the full pure-Lean pipeline
    2. Serde                  — the pure reader/writer reproduce the bytes
    3. Kernel anon roundtrip  — every constant through `Ix.Tc` ingress/egress
    4. Kernel meta roundtrip  — named entries against the Lean source, with
                                collapsed blocks routed through anonymous
                                mode (BB-F7)
    5. Decompile              — the full decompiler (inline records and
                                images included) against the source
    6. Oracle leg             — unchanged blocks: each Ix auxiliary equals
                                Lean's declaration of the same name compiled
                                by the same compiler, by address
    7. Image rules            — changed blocks: the stored images compute as
                                Lean's recursors (`rfl` in `Ix.Tc`), and the
                                Ix auxiliaries carry `_ix` names
    8. Provenance             — `Named.original` is Lean's form; nothing
                                un-surgered is stored but images
    9. Clique values          — every member of every transported
                                definition clique, as compiled, evaluates to
                                Lean's value on distinguishing inputs
                                (`Ix.Cli.CliqueValues`)

  Starting from a Lean FILE makes the Lean source the oracle of phases 4–9.
  With `--ixe <file>` (no Lean source) phases 1 and 4 are skipped, phases
  6–8 take Lean's forms from the decompiler's output (phase 5), which is a
  weaker oracle (the decompiler regenerates Lean's auxiliaries itself), and
  phase 9 is skipped (it evaluates Lean's own constants).

  `--local` validates the file's own constants with their closure (and the
  constants images and rule statements are built from: `PProd`, `And`,
  `True`, `Eq`), as `aux-cert` does; the default is the whole import
  environment (`--ns` filters by name prefix).

  Separate from the `lake test` binary for the same reason as `validate`:
  large files' transitive imports (e.g. Mathlib via
  `Benchmarks/Compile/CompileMathlib.lean`) must not become compile-time
  deps of the test suite.
-/
module
public import Cli
public import Ix.Common
public import Ix.CanonM
public import Ix.CompileM
public import Ix.CompileDriver
public import Ix.DecompileM
public import Ix.DecompileDriver
public import Ix.DecompileRoundtrip
public import Ix.Meta
public import Ix.Tc
public import Ix.Compile.Pass
public import Ix.Compile.Image
public import Ix.Cli.ValidateCmd
public import Ix.Cli.CliqueValues

public section

open System (FilePath)
open Ix.EnvScope

namespace Ix.Cli.ValidateLeanCmd

open Ix.Tc

/-- Phase outcome for the final report. -/
inductive PhaseResult where
  | passed (detail : String)
  | failed (detail : String)
  | stubbed (detail : String)
  | skipped (detail : String)

def PhaseResult.render : PhaseResult → String
  | .passed d => s!"PASS  {d}"
  | .failed d => s!"FAIL  {d}"
  | .stubbed d => s!"STUB  {d}"
  | .skipped d => s!"SKIP  {d}"

def PhaseResult.tag : PhaseResult → String
  | .passed _ => "PASS"
  | .failed _ => "FAIL"
  | .stubbed _ => "STUB"
  | .skipped _ => "SKIP"

def PhaseResult.isFailure : PhaseResult → Bool
  | .failed _ => true
  | _ => false

/-- One row of the phase table. -/
structure PhaseRow where
  key : String
  name : String
  result : PhaseResult
  ms : Nat := 0

/-- Append a phase result AND emit its section heading immediately, in
    `ix validate`'s style, flushing stdout. Incremental + flushed output is
    load-bearing: the stage-1 whole-Mathlib run was OOM-killed mid-phase
    with every completed phase's result still sitting in the block-buffered
    stdout, leaving no evidence of how far it got. Extra lines (the named
    exceptions of a phase) follow the result. -/
def pushPhase (phases : Array PhaseRow) (row : PhaseRow) (extra : Array String := #[]) :
    IO (Array PhaseRow) := do
  IO.println s!"[validate-lean] Phase: {row.key}. {row.name} ({row.ms} ms)"
  IO.println s!"  {row.result.render}"
  for l in extra do IO.println s!"    {l}"
  (← IO.getStdout).flush
  return phases.push row

/-! ## Shared context of phases 6–8 -/

/-- Lean's forms (canonicalized), the oracle of phases 6–8: from the Lean
    source in path mode, from the decompiler in `--ixe` mode. -/
abbrev View := Std.HashMap Ix.Name Ix.ConstantInfo

/-- The Lean member a reserved display name hangs off: the components before
    its first reserved one (`A._ix.rec ↦ A`, `rep₀._ix.rec_2 ↦ rep₀`). -/
def displayMember? (n : Ix.Name) : Option Ix.Name :=
  if !Ix.Compile.Pass.hasReserved n then none else
  let pre := (Ix.Compile.Pass.comps n).takeWhile fun c => match c with
    | .s x => !Ix.Compile.Pass.isReservedComponent x
    | .n _ => true
  if pre.isEmpty then none else some (Ix.Compile.Pass.ofComps pre)

/-- Path mode: the canonical forms of every Lean constant phases 6–8 read:
    the names of `env` that carry `Named.original`, the members display names
    hang off, and the inductive blocks of all of them (members,
    constructors, recursors). Computed while the Lean environment is live,
    so phase 5 can run without it. -/
def leanViewOf (leanEnv : Lean.Environment) (env : Ixon.Env) : View := Id.run do
  let mut want : Std.HashSet Ix.Name := {}
  for (n, nd) in env.named do
    if nd.original.isSome && !Ix.Compile.Pass.hasReserved n then want := want.insert n
    if let some x := displayMember? n then want := want.insert x
  let mut todo : Array Lean.Name := #[]
  for (ln, _) in leanEnv.constants.toList do
    if want.contains (Ix.Name.fromLeanName ln) then todo := todo.push ln
  let mut picked : Std.HashSet Lean.Name := {}
  let mut out : Array (Lean.Name × Lean.ConstantInfo) := #[]
  repeat
    match todo.back? with
    | none => break
    | some ln =>
      todo := todo.pop
      if picked.contains ln then continue
      let some ci := leanEnv.constants.find? ln | continue
      picked := picked.insert ln
      out := out.push (ln, ci)
      -- the inductives an auxiliary hangs off
      let mut p := ln.getPrefix
      while !p.isAnonymous do
        if let some (.inductInfo _) := leanEnv.constants.find? p then todo := todo.push p
        p := p.getPrefix
      match ci with
      | .inductInfo v =>
        for m in v.all do todo := todo.push m
        for c in v.ctors do todo := todo.push c
        for r in recursorsOf leanEnv ln do todo := todo.push r
      | .recInfo v => for m in v.all do todo := todo.push m
      | .ctorInfo v => todo := todo.push v.induct
      | _ => pure ()
  let chunkSize := max 64 ((out.size + 31) / 32)
  let tasks := (Ix.CanonM.chunks out chunkSize).map fun chunk =>
    Task.spawn fun _ => Ix.CanonM.canonChunk chunk
  let mut view : View := {}
  for t in tasks do
    for (n, ci) in t.get do view := view.insert n ci
  return view

/-- The changed blocks of a Pass 3 environment and the Lean auxiliaries that
    denote images (`Ix.Compile.Pass.imageKinds`, the compiler's own rule):
    a block is changed iff some member has `_ix` display entries. -/
structure Changed where
  blocks : Array (Array Ix.Name) := #[]
  members : Std.HashSet Ix.Name := {}
  images : Array Ix.Name := #[]
  imageSet : Std.HashSet Ix.Name := {}
  /-- Display members that are definitions, theorems or opaques: members of
      transported definition cliques, whose canonical constants carry `_ix`
      names (`f._ix._mutual`, `f._ix._f`, …). They have no images and no
      recursor rules, so phase 7 only counts them; the constants themselves
      are checked by the kernel phases and by decompile. -/
  cliques : Array Ix.Name := #[]
  /-- Display members whose block the view does not know. -/
  unknown : Array Ix.Name := #[]

def changedOf (env : Ixon.Env) (view : View) : Changed := Id.run do
  let mut ch : Changed := {}
  let mut seen : Std.HashSet Ix.Name := {}
  for (n, _) in env.named do
    let some x := displayMember? n | continue
    if seen.contains x then continue
    seen := seen.insert x
    match view.get? x with
    | some (.inductInfo v) =>
      if ch.members.contains x then continue
      ch := { ch with blocks := ch.blocks.push v.all
                      members := v.all.foldl (·.insert ·) ch.members }
      let imgs := Ix.Compile.Pass.imageKinds view.get? v.all
      ch := { ch with images := ch.images ++ imgs
                      imageSet := imgs.foldl (·.insert ·) ch.imageSet }
    | some (.defnInfo _) | some (.thmInfo _) | some (.opaqueInfo _) =>
      ch := { ch with cliques := ch.cliques.push x }
    | _ => ch := { ch with unknown := ch.unknown.push x }
  return ch

/-- How the compiler presented a Lean inductive block, read off the stored
    projections of its members: `identity` (one block, members at their
    source positions), or permuted, split, collapsed. It reads addresses
    only. -/
inductive Shape where
  | identity | permuted | split | collapsed | unknown
  deriving BEq, Inhabited

def Shape.name : Shape → String
  | .identity => "identity" | .permuted => "permuted" | .split => "split"
  | .collapsed => "collapsed" | .unknown => "unknown"

def blockShape (env : Ixon.Env) (all : Array Ix.Name) : Shape := Id.run do
  let keys := all.map fun a => (env.named.get? a).bind fun nd => projKey? env nd.addr
  if keys.any (·.isNone) then return (if all.size == 1 then .identity else .unknown)
  let ks := keys.filterMap id
  let some k0 := ks[0]? | return .unknown
  if ks.any (·.1 != k0.1) then return .split
  let idxs := ks.map (·.2.1)
  for i in [0:idxs.size] do
    for j in [i+1:idxs.size] do
      if idxs[i]! == idxs[j]! then return .collapsed
  if (idxs.zipIdx.any fun (k, i) => k.toNat != i) then return .permuted
  return .identity

/-! ## Recompiling Lean's own forms (phases 6 and 8) -/

/-- The inductive a regenerated auxiliary hangs off (`classifyAuxGen`), also
    for a constructor of a regenerated `IndPredBelow` inductive
    (`P.below.step ↦ P`, `P.below.s.t ↦ P` for a dotted constructor name),
    which carries `Named.original` too. -/
def auxRoot? (view : View) (n : Ix.Name) : Option Ix.Name :=
  let below? (i : Ix.Name) : Option Ix.Name := (Ix.AuxGen.classifyAuxGen i).bind fun (k, r) =>
    if k == Ix.AuxGen.AuxKind.below then some r else none
  match Ix.AuxGen.classifyAuxGen n with
  | some (_, r) => some r
  | none => match view.get? n with
    | some (.ctorInfo cv) => below? cv.induct
    | _ => match n with
      | .str p _ _ => below? p
      | _ => none

/-- The Lean compile unit of an auxiliary: the recursor family of its block
    for a recursor (`blockRecursors`), the inductive block with its
    constructors for an `IndPredBelow` inductive, the `all` of a
    definition. -/
def unitOf (view : View) (n : Ix.Name) : Option (Array Ix.Name) :=
  -- a constructor belongs to its inductive's unit
  let n := match view.get? n with
    | some (.ctorInfo cv) => cv.induct
    | _ => n
  match view.get? n with
  | some (.recInfo rv) =>
    match (rv.all[0]?).bind view.get? with
    | some (.inductInfo iv) =>
      let fam := Ix.Compile.Image.blockRecursors view.get? iv
      let fam := if fam.contains n then fam else fam.push n
      -- the strongly connected component of `n` in the family's reference
      -- graph (the rules' right-hand sides): the compiler compiles Lean's
      -- forms by SCC, so the recursors of a split block are separate units
      let refsOf (r : Ix.Name) : Array Ix.Name := match view.get? r with
        | some (.recInfo v) =>
          (v.rules.flatMap fun rule => Ix.Compile.Image.usedConstants rule.rhs).filter fam.contains
        | _ => #[]
      let reach (a : Ix.Name) : Std.HashSet Ix.Name := Id.run do
        let mut seen : Std.HashSet Ix.Name := ({} : Std.HashSet Ix.Name).insert a
        let mut todo := #[a]
        for _ in [0:fam.size + 1] do
          let mut next := #[]
          for x in todo do
            for y in refsOf x do
              if !seen.contains y then
                seen := seen.insert y
                next := next.push y
          todo := next
        return seen
      let fromN := reach n
      some (fam.filter fun r => fromN.contains r && (reach r).contains n)
    | _ => some #[n]
  | some (.inductInfo iv) =>
    some (iv.all ++ iv.all.flatMap fun m => match view.get? m with
      | some (.inductInfo v) => v.ctors
      | _ => #[])
  | some (.defnInfo v) => some (if v.all.contains n then v.all else #[n])
  | some (.thmInfo v) => some (if v.all.contains n then v.all else #[n])
  | some (.opaqueInfo v) => some (if v.all.contains n then v.all else #[n])
  | _ => none

/-- A synthetic compile environment over `view` whose names resolve to the
    addresses of `env` (the decompiler's `cenvFor`): what the compiler's
    resolution map held when it compiled Lean's forms. -/
def cenvOver (env : Ixon.Env) (view : View) (limits : Ix.Sharing.Exact.Limits) :
    Ix.CompileM.CompileEnv :=
  { env := { consts := view }
    nameToNamed := env.named
    nameToAddr := env.named.fold (init := {}) fun m n nd => m.insert n nd.addr
    sharingLimits := limits
    constants := {}, blobs := {}, totalBytes := 0 }

/-- Compile one unit in Lean's own form (no auxiliary regeneration, no
    rewrite: `compileConstNoAuxPure`, the compiler's promotion compile) and
    return each member's address. -/
def recompileUnit (cenv : Ix.CompileM.CompileEnv) (members : Array Ix.Name) :
    Except String (Array (Ix.Name × Address)) := do
  let some lo := members[0]? | throw "empty unit"
  let all : Ix.Set Ix.Name := members.foldl (·.insert ·) {}
  match Ix.CompileM.compileConstNoAuxPure cenv lo all with
  | .error e => throw (toString e)
  | .ok (res, _) =>
    if res.projections.isEmpty then return #[(lo, res.blockAddr)]
    return res.projections.map fun (n, proj, _) => (n, Address.blake3 (Ixon.ser proj))

/-- Lean-form addresses of `names` (grouped into units, compiled in
    parallel), with the failures by unit. -/
structure Recompiled where
  addrs : Std.HashMap Ix.Name Address := {}
  failed : Std.HashMap Ix.Name String := {}
  units : Nat := 0

def recompileAll (cenv : Ix.CompileM.CompileEnv) (view : View) (names : Array Ix.Name) :
    Recompiled := Id.run do
  let mut units : Array (Array Ix.Name) := #[]
  let mut covered : Std.HashSet Ix.Name := {}
  let mut failed : Std.HashMap Ix.Name String := {}
  for n in names do
    if covered.contains n then continue
    match unitOf view n with
    | none => failed := failed.insert n "Lean's form is not in the oracle"
    | some u =>
      units := units.push u
      covered := u.foldl (·.insert ·) covered
  let chunkSize := max 1 ((units.size + 63) / 64)
  let tasks := (Ix.CanonM.chunks units chunkSize).map fun chunk =>
    Task.spawn fun _ => chunk.map fun u => (u, recompileUnit cenv u)
  let mut out : Recompiled := { failed, units := units.size }
  for t in tasks do
    for (u, r) in t.get do
      match r with
      | .ok xs => for (n, a) in xs do out := { out with addrs := out.addrs.insert n a }
      | .error e =>
        for n in u do out := { out with failed := out.failed.insert n e }
  return out

/-! ## Rule statements of Lean's recursors (phase 7) -/

section Rules
open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Image
open Ix.Compile.Canon (mkAppN substLevels)

/-- One computation rule of a Lean recursor `r`, stated over the constant
    `r` of the environment (which, for a changed block under Pass 3, is
    `r`'s stored image): `∀ ps ms mins fs, r ps ms mins is (c ps fs) =
    rhs ps ms mins fs`, with proof `λ …, Eq.refl _`. The same statement the
    `pass3` suite checks (`Ix.Compile.Image.RuleStmt`), built from Lean's
    `RecursorVal` alone, so it applies to any `.ixe`. -/
def leanRuleStmts (const? : Name → Option ConstantInfo) (r : Name) :
    Except String (Array RuleStmt) := GenM.run' do
  let rv ← Ix.Compile.Image.liftExcept (recOf const? r)
  let (xs, body) ← telescope rv.cnst.type
  let np := rv.numParams
  let nm := rv.numMotives
  let nmin := rv.numMinors
  let pmm := xs.extract 0 (np + nm + nmin)
  let is := xs.extract (np + nm + nmin) (xs.size - 1)
  let some x := xs.back? | throw s!"{r.pretty}: recursor without a major"
  let some m0 := xs[np]? | throw s!"{r.pretty}: recursor without motives"
  let lu := motiveLevel m0.type
  let lps := rv.cnst.levelParams
  let recC := Expr.mkConst r (lps.map Level.mkParam)
  let T := x.type
  let some (_, tLvls) := headConst? T | throw s!"{r.pretty}: major type's head"
  let mut out : Array RuleStmt := #[]
  for rule in rv.rules do
    let cv ← Ix.Compile.Image.liftExcept (ctorOf const? rule.ctor)
    let cParams := (getAppArgs T).extract 0 cv.numParams
    let ctorC := Expr.mkConst rule.ctor tLvls
    let cty ← Ix.Compile.Image.liftExcept (instForall (substLevels cv.cnst.levelParams tLvls cv.cnst.type) cParams)
    let (flds, cres) ← telescope cty
    let idx := (getAppArgs cres).extract cv.numParams (getAppArgs cres).size
    let major := mkAppN ctorC (cParams ++ flds.map (·.expr))
    let lhs := mkAppN recC (pmm.map (·.expr) ++ idx ++ #[major])
    let rhs ← Ix.Compile.Image.liftExcept (instantiate rule.rhs (pmm.map (·.expr) ++ flds.map (·.expr)))
    let α ← Ix.Compile.Image.liftExcept (substFVars ((is.push x).map (·.fvar)) (idx.push major) body)
    let eq := mkAppN (Expr.mkConst nEq #[lu]) #[α, lhs, rhs]
    let refl := mkAppN (Expr.mkConst nEqRefl #[lu]) #[α, lhs]
    out := out.push {
      ctor := rule.ctor
      name := Name.mkStr (Name.mkStr r "_ix_rule") (lastStr rule.ctor)
      levelParams := lps
      type := mkForall (pmm ++ flds) eq
      proof := mkLambda (pmm ++ flds) refl }
  return out

end Rules

/-- Compile a theorem into a copy of `env` (constant, blobs; no `Named`
    entry is needed by the anonymous checker). Returns its address. -/
def addTheorem (cenv : Ix.CompileM.CompileEnv) (env : Ixon.Env) (s : Ix.Compile.Image.RuleStmt) :
    Except String (Ixon.Env × Address) := do
  let tv : Ix.TheoremVal := {
    cnst := { name := s.name, levelParams := s.levelParams, type := s.type }
    value := s.proof, all := #[s.name] }
  let blockEnv : Ix.CompileM.BlockEnv :=
    { all := ({} : Ix.Set Ix.Name).insert s.name, current := s.name,
      mutCtx := default, univCtx := [] }
  match Ix.CompileM.CompileM.run cenv blockEnv {} (Ix.CompileM.compileConstantInfo (.thmInfo tv)) with
  | .error e => throw s!"{s.name.pretty}: {e}"
  | .ok (r, bs) =>
    let env := { env with
      consts := env.consts.insert r.blockAddr { buf := r.blockBytes, len := r.blockBytes.size }
      blobs := bs.blockBlobs.fold (fun m k v => m.insert k v) env.blobs }
    return (env, r.blockAddr)

/-! ## Explaining an oracle-leg exception (`IX_VALIDATE_EXPLAIN=1`) -/

/-- The first position at which two `∀`/`λ` telescopes differ: the binder
    index (with its name on each side), or `body`. -/
partial def telescopeDiff (a b : Ix.Expr) (i : Nat := 0) : String :=
  match a, b with
  | .forallE na ta ba _ _, .forallE nb tb bb _ _ =>
    if ta != tb then s!"binder #{i} ({na.pretty} vs {nb.pretty})" else telescopeDiff ba bb (i + 1)
  | .lam na ta ba _ _, .lam nb tb bb _ _ =>
    if ta != tb then s!"binder #{i} ({na.pretty} vs {nb.pretty})" else telescopeDiff ba bb (i + 1)
  | _, _ => if a == b then "equal" else s!"body after {i} binders"

/-- How the Ix auxiliary stored under `n` (decompiled from its own bytes and
    metadata, not from the original) differs from Lean's form: recursor
    shape, rule order, the first differing binder of the type, the first
    differing rule. -/
def explainDiff (env : Ixon.Env) (view : View) (n : Ix.Name) : String := Id.run do
  let some nd := env.named.get? n | return "not stored"
  let some lean := view.get? n | return "Lean's form unknown"
  let dec : Except String (Array (Ix.Name × Ix.ConstantInfo)) :=
    Ix.DecompileM.decompileOne { ixonEnv := env } env n { nd with original := none }
  let ix? : Option Ix.ConstantInfo := match dec with
    | .ok xs => (xs.find? (·.1 == n)).map (·.2)
    | .error _ => none
  let some ix := ix? | return "the Ix auxiliary does not decompile on its own"
  match lean, ix with
  | .recInfo a, .recInfo b =>
    let shape := s!"params {a.numParams}/{b.numParams} motives {a.numMotives}/{b.numMotives} \
minors {a.numMinors}/{b.numMinors} indices {a.numIndices}/{b.numIndices} k {a.k}/{b.k} \
unsafe {a.isUnsafe}/{b.isUnsafe}"
    let ctorsA := a.rules.map (·.ctor.pretty)
    let ctorsB := b.rules.map (·.ctor.pretty)
    let rules := if ctorsA != ctorsB then s!"rule order {ctorsA} vs {ctorsB}"
      else match (a.rules.zip b.rules).findIdx? (fun (x, y) => x.rhs != y.rhs) with
        | some i => match a.rules[i]?, b.rules[i]? with
          | some x, some y => s!"rule #{i} rhs: {telescopeDiff x.rhs y.rhs}"
          | _, _ => "rules differ"
        | none => "rules equal"
    return s!"recursor (Lean/Ix) {shape}; type: {telescopeDiff a.cnst.type b.cnst.type}; {rules}; \
all {a.all.map (·.pretty)} vs {b.all.map (·.pretty)}"
  | .defnInfo a, .defnInfo b =>
    return s!"definition; type: {telescopeDiff a.cnst.type b.cnst.type}; value: {telescopeDiff a.value b.value}"
  | .inductInfo a, .inductInfo b =>
    return s!"inductive; type: {telescopeDiff a.cnst.type b.cnst.type}; ctors {a.ctors.map (·.pretty)} vs {b.ctors.map (·.pretty)}; all {a.all.map (·.pretty)} vs {b.all.map (·.pretty)}"
  | .ctorInfo a, .ctorInfo b =>
    return s!"constructor; type: {telescopeDiff a.cnst.type b.cnst.type}"
  | _, _ => return "different kinds"

/-! ## The phases -/

/-- Up to `k` names, pretty-printed. -/
def showNames (ns : Array Ix.Name) (k : Nat := 8) : String :=
  let shown := (ns.extract 0 k).map (·.pretty)
  let more := if ns.size > k then s!", … ({ns.size - k} more)" else ""
  s!"[{", ".intercalate shown.toList}{more}]"

/-- **Phase 4, the kernel meta roundtrip.** Establishes, for every named
    entry compared, that `Ix.Tc`'s meta-mode ingress and egress reproduce the
    canonicalized Lean source constant exactly (type, value, rules, names,
    binder information, metadata), so the stored metadata is faithful. It
    does NOT compare entries that carry `Named.original` (regenerated
    auxiliaries and images: phases 6–8), entries with altering call-site
    surgery or a Pass 3 `_ix.inline` record (their term is the rewritten
    form; phase 5 restores the source), or `_ix` display entries (aliases,
    no Lean counterpart). Blocks the compiler collapsed are routed: the
    meta-mode ingress loses a collapsed member (BB-F7, pre-existing), so
    they are roundtripped in anonymous mode (gated) and their meta-mode
    verdicts are reported, not gated. Every other ingress failure is
    charged to its block and fails the phase. -/
def phaseMeta (leanEnv : Lean.Environment) (parts : Ixon.LazyEnvParts) :
    IO (PhaseResult × Array String) := do
  -- Collapsed blocks: a `Muts` member several names project to, and a class
  -- the compiler emitted as one standalone constant (members of one Lean
  -- mutual `all` sharing an address, e.g. the `_unsafe_rec` definitions over
  -- a collapsed inductive pair).
  let rowAddr (n : Ix.Name) : Option Address := (parts.rowIdx.get? n).bind fun i =>
    (parts.namedRows[i]?).map (·.addr)
  let standalone : Std.HashSet Address := Id.run do
    let mut out : Std.HashSet Address := {}
    for (ln, ci) in leanEnv.constants.toList do
      let all := match ci with
        | .defnInfo v => v.all
        | .thmInfo v => v.all
        | .opaqueInfo v => v.all
        | _ => []
      if all.length < 2 || all.head? != some ln then continue
      let addrs := all.filterMap fun m => rowAddr (Ix.Name.fromLeanName m)
      let mut seen : Std.HashSet Address := {}
      for a in addrs do
        if seen.contains a && (projKey? parts.env a).isNone then out := out.insert a
        seen := seen.insert a
    return out
  let routed := standalone.fold (·.insert ·) (collapsedBlocks parts)
  let report ← match ← IO.getEnv "IX_META_EAGER" with
    | some _ =>
      pure <| parts.materializeAllNamed.bind fun fullEnv => metaRoundtripEnv leanEnv fullEnv
    | none => pure <| metaRoundtripEnvStreaming leanEnv parts (routed := routed)
  match report with
  | .error e => return (.failed e, #[])
  | .ok report =>
    -- the anonymous leg of the routed blocks
    let mut anonOk := 0
    let mut anonFail : Array String := #[]
    for b in report.routedBlocks do
      match buildAnonWorkItem parts.env b with
      | .ok (some item) =>
        let rows := roundtripWorkItem parts.env item
        match rows.find? (·.err?.isSome) with
        | some r => anonFail := anonFail.push s!"{b}: {r.err?.getD ""}"
        | none => anonOk := anonOk + 1
      | .ok none => anonFail := anonFail.push s!"{b}: no anonymous work item"
      | .error e => anonFail := anonFail.push s!"{b}: {e}"
    let counts := s!"checked {report.checked}, notFound {report.notFound}, \
display {report.display}, skippedAux {report.skippedAux}, \
skippedSurgery {report.skippedSurgery}"
    let routedLine := s!"BB-F7 route-around: {report.routedBlocks.size} collapsed block(s), \
{report.routedRows} row(s); anonymous roundtrip {anonOk}/{report.routedBlocks.size} pass; \
meta mode on them (reported, not gated): {report.routedChecked} equal, \
{report.routedErrorCount} fail"
    let mut lines : Array String := #[routedLine]
    for (n, m) in report.routedErrors.toList.take 4 do
      lines := lines.push s!"BB-F7 (meta, not gated) {n.pretty}: {m.take 160}"
    for f in anonFail.toList.take 4 do lines := lines.push s!"✗ anonymous leg {f}"
    for (n, m) in report.errors.toList.take 6 do
      lines := lines.push s!"✗ {n.pretty}: {m.take 200}"
    if report.errorCount == 0 && anonFail.isEmpty then
      return (.passed s!"{counts}; {report.routedBlocks.size} collapsed block(s) via anonymous mode", lines)
    let ids := (if report.errorCount == 0 then [] else [s!"meta {report.errorCount}"])
      ++ (if anonFail.isEmpty then [] else [s!"anonymous leg {anonFail.size}"])
    return (.failed s!"{report.errorCount} comparison error(s) ({", ".intercalate ids}); {counts}", lines)

/-- **Phase 6, the oracle leg for unchanged blocks.** Establishes, for every
    regenerated auxiliary (`rec`, `rec_N`, `casesOn`, `recOn`, `below*`,
    `brecOn*`, `.go`, `.eq`) of an inductive block the compiler presented
    unchanged (one block, members at their source positions: `blockShape`
    `identity`, and no `_ix` display entry), that the Ix auxiliary stored
    under the name is byte-identical, by address, to Lean's own declaration
    of the same name compiled by the same compiler in its own form (the
    promotion compile, `compileConstNoAuxPure`, over the output's name
    resolution); and, in path mode, that the auxiliary names agree both
    ways (§4.7(b): Ix generates an auxiliary iff Lean has it). It does not
    check auxiliaries of changed blocks (their Lean names denote images
    under Pass 3, phase 7; or, in a file the legacy surgery wrote before M6R
    slice 6, name surgered Ix auxiliaries, which are reported by block
    shape), Lean's non-regenerated
    auxiliaries (`noConfusion`, `sizeOf`, …: ordinary constants, phase 4),
    and it is only as independent as the shared compiler (the `aux-oracle`
    suite's `Gen.lean` replay is the independent leg, on fixtures). In
    a Pass 3 compile a changed block without `_ix` names fails the phase. -/
def phaseOracle (env : Ixon.Env) (view : View) (ch : Changed) (rc : Recompiled)
    (leanAux? : Option (Std.HashSet Ix.Name)) (ungrounded : Std.HashSet Ix.Name := {})
    (pass3 : Bool := false) (explain : Bool := false) :
    PhaseResult × Array String := Id.run do
  let mut subjects := 0
  let mut equal := 0
  let mut mismatch : Array (Ix.Name × String) := #[]
  let mut changedNonImage : Array Ix.Name := #[]
  let mut surgery : Std.HashMap String (Array Ix.Name) := {}
  let mut shapes : Std.HashMap Ix.Name Shape := {}
  for (n, nd) in env.named do
    if Ix.Compile.Pass.hasReserved n || nd.original.isNone then continue
    if ch.imageSet.contains n then continue
    let some root := auxRoot? view n | continue
    if ch.members.contains root then
      changedNonImage := changedNonImage.push n
      continue
    let shape := match shapes.get? root with
      | some s => s
      | none => match view.get? root with
        | some (.inductInfo v) => blockShape env v.all
        | _ => Shape.unknown
    shapes := shapes.insert root shape
    if shape != .identity then
      surgery := surgery.insert shape.name ((surgery.getD shape.name #[]).push root)
      continue
    subjects := subjects + 1
    match rc.addrs.get? n with
    | some a =>
      if a == nd.addr then equal := equal + 1
      else mismatch := mismatch.push (n, s!"Lean's form {(toString a).take 12} ≠ Ix auxiliary {(toString nd.addr).take 12}")
    | none => mismatch := mismatch.push (n, s!"Lean's form not compiled: {(rc.failed.getD n "no unit").take 200}")
  -- §4.7(b), existence, both ways (path mode: the compiled input is known)
  let mut leanOnly : Array Ix.Name := #[]
  let mut ixOnly : Array Ix.Name := #[]
  if let some leanAux := leanAux? then
    for n in leanAux do
      if !env.named.contains n && !ungrounded.contains n then leanOnly := leanOnly.push n
    for (n, nd) in env.named do
      if Ix.Compile.Pass.hasReserved n || nd.original.isSome then continue
      if Ix.AuxGen.isAuxGenSuffix n && !leanAux.contains n then
        -- only an auxiliary of an inductive the input has is Ix-generated
        if let some (_, root) := Ix.AuxGen.classifyAuxGen n then
          if env.named.contains root then ixOnly := ixOnly.push n
  let dedup (xs : Array Ix.Name) : Array Ix.Name :=
    (xs.foldl (fun (s : Std.HashSet Ix.Name) x => s.insert x) {}).toArray
  let surgeryLine := ", ".intercalate (surgery.toList.map fun (k, rs) =>
    s!"{k} {(dedup rs).size}")
  let mut lines : Array String := #[]
  for (n, m) in mismatch.toList.take 8 do
    lines := lines.push s!"✗ {n.pretty}: {m}"
    if explain then lines := lines.push s!"    explain: {explainDiff env view n}"
  if !leanOnly.isEmpty then
    lines := lines.push s!"✗ §4.7(b) Lean auxiliary absent from the output: {showNames leanOnly}"
  if !ixOnly.isEmpty then
    lines := lines.push s!"✗ §4.7(b) Ix auxiliary Lean does not have: {showNames ixOnly}"
  if !surgery.isEmpty then
    lines := lines.push s!"changed blocks without `_ix` names (legacy surgery output, not an \
oracle subject): {surgeryLine}"
    for (k, rs) in surgery.toList do lines := lines.push s!"  {k}: {showNames (dedup rs) 6}"
  if !changedNonImage.isEmpty then
    lines := lines.push s!"auxiliaries of changed blocks that are not images (phase 8 checks \
their provenance): {showNames changedNonImage}"
  let detail := s!"{equal}/{subjects} auxiliaries of unchanged blocks equal Lean's own by address \
({rc.units} Lean units recompiled); §4.7 classes: (b) existence {leanOnly.size + ixOnly.size}, \
unclassified {mismatch.size}; changed blocks skipped: {(if surgeryLine.isEmpty then "none" else surgeryLine)}, \
{ch.blocks.size} with images"
  -- under Pass 3 a changed block has `_ix` names and images: none may be on
  -- the surgery path
  if pass3 && !surgery.isEmpty then
    return (.failed s!"changed block(s) without `_ix` names under Pass 3 ({surgeryLine}); {detail}", lines)
  if mismatch.isEmpty && leanOnly.isEmpty && ixOnly.isEmpty then
    return (.passed detail, lines)
  return (.failed detail, lines)

/-- **Phase 7, the image rules of changed blocks.** Establishes, for every
    changed block of a Pass 3 environment (a block some member of which has
    `_ix` display entries), that (i) every Lean auxiliary of an image kind
    (`imageKinds`, the compiler's rule) is stored under its Lean name as a
    definition carrying `Named.original` (the image, decision 3); (ii) the
    Ix auxiliaries carry `_ix` names (`x._ix.S` exists for every image `x.S`
    that is not a nested-position kind, `x` the longest member of the image's
    block prefixing it); (iii) every image and every
    computation rule of every Lean recursor of the block, stated over the
    stored image (`leanRuleStmts`: `r ps ms mins is (c ps fs) = rhs`, proof
    `Eq.refl`), is accepted by `Ix.Tc` in anonymous mode, in a test-only
    copy of the environment. It does not check the non-recursor images'
    equations (they are Lean's own values over the images, Def 3.5, checked
    as constants here and by decompile in phase 5), and on a file the
    legacy surgery wrote it does not apply (no images; reported by phase
    6). -/
def phaseRules (env : Ixon.Env) (view : View) (ch : Changed) (limits : Ix.Sharing.Exact.Limits)
    (ungrounded : Std.HashSet Ix.Name := {}) :
    PhaseResult × Array String × Array String := Id.run do
  let cliqueNote := if ch.cliques.isEmpty then ""
    else s!"; {ch.cliques.size} clique display member(s), not image-checked here"
  if ch.blocks.isEmpty then
    return (.skipped ((if ch.unknown.isEmpty then "no changed block with `_ix` names (no block changed, or legacy surgery output)"
      else s!"display members without a Lean block: {showNames ch.unknown}") ++ cliqueNote), #[], #[])
  -- a block Pass 2 refused (its compile failed, phase 1) has no images to check
  let live := ch.blocks.filter fun all =>
    !(all.any ungrounded.contains) && !((Ix.Compile.Pass.imageKinds view.get? all).any ungrounded.contains)
  let images := live.flatMap (Ix.Compile.Pass.imageKinds view.get?)
  -- each image's Lean block: its display name hangs off the longest member
  -- of that block prefixing it (the compiler's rule, `ixAuxName`), so the
  -- `IndPredBelow` family's `x.below.rec` is displayed `x.below._ix.rec`
  -- when the family is the changed block (A3V-IPB)
  let blockOf : Std.HashMap Ix.Name (Array Ix.Name) := live.foldl (init := {}) fun m all =>
    (Ix.Compile.Pass.imageKinds view.get? all).foldl (init := m) fun m n => m.insert n all
  let refused := ch.blocks.size - live.size
  let mut problems : Array String := #[]
  let mut checkAddrs : Array (Address × String) := #[]
  for n in images do
    let some nd := env.named.get? n
      | problems := problems.push s!"{n.pretty}: image not stored"; continue
    if nd.original.isNone then problems := problems.push s!"{n.pretty}: image without Named.original"
    let isDefn := match env.getConst? nd.addr with
      | some c => match c.info with
        | .defn _ | .dPrj _ => true
        | _ => false
      | none => false
    if !isDefn then problems := problems.push s!"{n.pretty}: stored constant is not a definition"
    -- the display name of the Ix auxiliary
    let root? : Option Ix.Name := (blockOf.get? n).bind fun all =>
      (all.foldl (init := (none : Option (Ix.Name × Nat))) fun best x =>
        match Ix.Compile.Pass.stripPrefix? x n with
        | some rest =>
          if rest.isEmpty then best
          else match best with
            | some (_, k) => if rest.length < k then some (x, rest.length) else best
            | none => some (x, rest.length)
        | none => best).map (·.1)
    if let some root := root? then
      let rest := (Ix.Compile.Pass.stripPrefix? root n).getD []
      let nested := match rest.head? with
        | some c => (Ix.Compile.Pass.nestedComp? c).isSome
        | none => false
      if !nested then
        let disp := Ix.Compile.Pass.appendComps (Ix.Name.mkStr root Ix.Compile.Pass.ixComponent) rest
        if !env.named.contains disp then problems := problems.push s!"{n.pretty}: no display entry {disp.pretty}"
    checkAddrs := checkAddrs.push (nd.addr, n.pretty)
  for x in ch.unknown do problems := problems.push s!"display member {x.pretty} has no Lean block"
  -- the rule statements, compiled into a copy of the environment
  let cenv := cenvOver env view limits
  let mut renv := env
  let mut nRules := 0
  let mut nRecs := 0
  for n in images do
    let some (.recInfo _) := view.get? n | continue
    nRecs := nRecs + 1
    match leanRuleStmts view.get? n with
    | .error e => problems := problems.push s!"{n.pretty}: rule statements: {e}"
    | .ok stmts =>
      for s in stmts do
        match addTheorem cenv renv s with
        | .error e => problems := problems.push s!"{s.name.pretty}: {e.take 200}"
        | .ok (renv', a) =>
          renv := renv'
          nRules := nRules + 1
          checkAddrs := checkAddrs.push (a, s.name.pretty)
  let verdicts := checkAnonAddrs renv (checkAddrs.map (·.1))
  let mut rejected := 0
  for ((_, label), (_, v)) in checkAddrs.zip verdicts do
    if let some e := v then
      rejected := rejected + 1
      problems := problems.push s!"{label}: Ix.Tc rejects: {e.take 200}"
  let detail := s!"{ch.blocks.size} changed block(s) ({refused} refused by Pass 2, phase 1), {images.size} image(s) ({nRecs} of recursors), \
{nRules} computation rule(s) by rfl; Ix.Tc (anonymous) accepts {checkAddrs.size - rejected}/{checkAddrs.size}{cliqueNote}"
  let lines := (problems.extract 0 12).map ("✗ " ++ ·)
  if problems.isEmpty then return (.passed detail, lines, problems)
  return (.failed s!"{problems.size} problem(s); {detail}", lines, problems)

/-- **Phase 8, provenance.** Establishes that (i) `Named.original` of every
    image (and of every other auxiliary of a changed block) is the address
    of Lean's auxiliary compiled in its own form (recompiled here, over the
    output's name resolution, as the compiler's promotion compile does);
    (ii) for every regenerated auxiliary of an unchanged block it equals the
    constant's own address (no packaging difference remains after A2);
    (iii) no stored constant's bytes are an un-surgered original: an
    `original` address that differs from its entry's address is not stored
    unless it is some name's canonical address (the Rust phase 3 rule);
    (iv) only regenerated auxiliary names carry `original`, and every image
    has one. Every violation is reported by name. It does not re-derive the
    surgered originals of a file the legacy surgery wrote (their provenance
    is the surgery replay, checked by phase 5). -/
def phaseProvenance (env : Ixon.Env) (view : View) (ch : Changed) (rc : Recompiled) :
    PhaseResult × Array String := Id.run do
  let canonical : Std.HashSet Address := env.named.fold (init := {}) fun s _ nd => s.insert nd.addr
  let mut violations : Array String := #[]
  let mut nImg := 0
  let mut nAux := 0
  let mut nSurg := 0
  let mut nWith := 0
  for (n, nd) in env.named do
    let some (oa, _) := nd.original | continue
    nWith := nWith + 1
    if Ix.Compile.Pass.hasReserved n then
      violations := violations.push s!"{n.pretty}: a display entry carries Named.original"
      continue
    let some root := auxRoot? view n
      | violations := violations.push s!"{n.pretty}: Named.original on a constant that is not a regenerated auxiliary"
        continue
    -- (iii) the ephemeral original is never stored
    if oa != nd.addr && env.consts.contains oa && !canonical.contains oa then
      violations := violations.push s!"{n.pretty}: original {(toString oa).take 12} is stored (un-surgered original leaked)"
    if ch.imageSet.contains n || ch.members.contains root then
      -- (i) the image's original is Lean's own form
      nImg := nImg + 1
      match rc.addrs.get? n with
      | some a =>
        if a != oa then
          violations := violations.push s!"{n.pretty}: Named.original {(toString oa).take 12} ≠ Lean's form compiled {(toString a).take 12}"
      | none => violations := violations.push s!"{n.pretty}: Lean's form not compiled: {(rc.failed.getD n "no unit").take 160}"
    else
      let shape := match view.get? root with
        | some (.inductInfo v) => blockShape env v.all
        | _ => Shape.unknown
      if shape == .identity then
        -- (ii) no packaging difference
        nAux := nAux + 1
        if oa != nd.addr then
          violations := violations.push s!"{n.pretty}: Named.original {(toString oa).take 12} ≠ own address {(toString nd.addr).take 12} (unchanged block)"
      else
        nSurg := nSurg + 1
  -- (iv) every image has an original
  for n in ch.images do
    if let some nd := env.named.get? n then
      if nd.original.isNone then violations := violations.push s!"{n.pretty}: image without Named.original"
  let detail := s!"{nWith} entries with Named.original: {nImg} images/changed-block auxiliaries \
(original = Lean's form recompiled), {nAux} unchanged-block auxiliaries (original = own address), \
{nSurg} surgered (legacy surgery output, not re-derived); {violations.size} violation(s)"
  let lines := (violations.extract 0 12).map ("✗ " ++ ·)
  if violations.isEmpty then return (.passed detail, lines)
  return (.failed detail, lines)

/-- The transported definition cliques of a compile, read from the
    compiler's clique record (the reference reader is the `pass3-cliques`
    suite, `Tests/Ix/Compile/Pass3Cliques.lean`): every clique of the
    switch-on clique table (`CompileEnv.p3Cliques`, member ↦ (the clique in
    Lean's order, its carried lemmas), each clique once under its first
    member) whose plan, recomputed by the compiler's own planner
    (`Ix.Compile.Pass.planClique`, as the clique hook and the callers' check
    compute it), is `transported`. Not from `_ix` names: the passes O7–O12
    store canonical forms under `c._ix` and helper names (`p._ix_retyped.s`,
    `T.noConfusionType._ix`, …), which are recorded in the non-canonical set
    (`PJ-FORM-<pass>`, `INHERITED`) and never in the clique table, so they are
    excluded by construction. Empty without a Pass 3 compile (no table). Sorted by
    first member, so the phase's order is the same on every run. -/
def transportedCliques (cenv : Ix.CompileM.CompileEnv) : Array (Array Lean.Name) := Id.run do
  let mut out : Array (Array Ix.Name) := #[]
  for (n, (cl, carried)) in cenv.p3Cliques.toList do
    unless cl[0]? == some n do continue
    match Ix.Compile.Pass.planClique cenv.env.get? (Ix.Compile.Pass.cliqueAddr cenv) cl carried with
    | .transported _ => out := out.push cl
    | _ => pure ()
  let sorted := out.qsort fun a b => (a[0]?.map (·.pretty)).getD "" < (b[0]?.map (·.pretty)).getD ""
  return sorted.map (·.map IxCliqueValues.toLeanName)

/-- **Phase 9, clique values** (`Ix.Cli.CliqueValues`, plan M4 (b)).
    Establishes, for every transported definition clique of the output (the
    compiler's clique record, `transportedCliques`) and every member, that the
    COMPILED member (decompiled from the output's bytes without replaying
    its `_ix.inline` record, i.e. the stored transported term, with the
    canonical constants it reaches, all added to Lean's environment through
    Lean's kernel) evaluates to Lean's value on distinguishing inputs
    derived from the member's type (fixpoints one unfolding deep, with a
    free-variable oracle per member placed by the side-car `σ`). Members
    that cannot be evaluated (theorems, propositions, opaque, structural
    without closed data, resource limits) are reported with the reason and
    counted; every member has a verdict. A clique the record calls
    transported whose compiled constants carry no side-car record
    `_ix.clique` fails. It does not check equation lemmas carried with a
    clique, Lean's encoding constants (kept in Lean's form), the O7–O12
    canonical forms (`c._ix`: not cliques), or values deeper than one
    fixpoint unfolding; it needs the Lean source and the compile (path
    mode). `ixDefs` counts the definition, theorem and opaque display members
    of `_ix` names (`Changed.cliques`: transported members and the O7–O12
    forms alike); a skip reports it, so a run whose output has `_ix` forms and
    no transported clique shows both (the suite's control). -/
def phaseCliqueValues (leanEnv : Lean.Environment) (ixonEnv : Ixon.Env) (cliques : Array (Array Lean.Name))
    (ixDefs : Nat) : IO (PhaseResult × Array String) := do
  if cliques.isEmpty then
    return (.skipped s!"no transported definition clique in the compiler's clique record \
      ({ixDefs} definition display member(s) of `_ix` names, none of a transported clique)", #[])
  let rep ← IxCliqueValues.run leanEnv ixonEnv cliques
  let (failed, detail, lines) := IxCliqueValues.summarize rep
  return (if failed then .failed detail else .passed detail, lines)

/-! ## The auxiliary table (`IX_VALIDATE_AUXTABLE=<path>`) -/

/-- One TSV row per regenerated auxiliary and image of `env`: its name, the
    block's status (`unchanged`, `permuted`, `split`, `collapsed`,
    `nested-order` for a changed block whose members keep their positions,
    `unknown`), whether its address differs from Lean's own form (the
    recompiled form, else `Named.original`), the phase that handles it, and
    that phase's verdict for it. The evidence table of A3v's follow-up (which
    phase covers each auxiliary that is not identical to Lean's). -/
def auxTableRows (env : Ixon.Env) (view : View) (ch : Changed) (rc : Recompiled)
    (rulesProblems : Array String) (pass3 : Bool) : Array String := Id.run do
  let mut rows : Array String := #["name\tstatus\tdiffers\tphase\tverdict"]
  for (n, nd) in env.named do
    if Ix.Compile.Pass.hasReserved n then continue
    if nd.original.isNone && !ch.imageSet.contains n then continue
    let leanAddr := (rc.addrs.get? n).orElse fun _ => nd.original.map (·.1)
    let differs := leanAddr != some nd.addr
    let root? := auxRoot? view n
    let shape := match root?.bind view.get? with
      | some (.inductInfo v) => blockShape env v.all
      | _ => Shape.unknown
    let changed := match root? with
      | some r => ch.members.contains r
      | none => false
    let status := if changed then (if shape == .identity then "nested-order" else shape.name)
      else if shape == .identity then "unchanged" else shape.name
    let routed := if shape == .collapsed then "; 4: anonymous roundtrip (BB-F7 route)" else ""
    let (phase, verdict) : String × String :=
      if ch.imageSet.contains n then
        let failed := rulesProblems.any fun p =>
          p.startsWith (n.pretty ++ ":") || p.startsWith (n.pretty ++ "._ix_rule.")
        ("7 image rules" ++ routed, if failed then "fail" else "pass")
      else if changed then
        let ok := match nd.original with
          | some (oa, _) => rc.addrs.get? n == some oa
          | none => false
        ("8 provenance (changed-block auxiliary, not an image)" ++ routed, if ok then "pass" else "fail")
      else if shape == .identity then
        ("6 oracle leg" ++ routed, if differs then "exception" else "equal")
      else if pass3 then ("6 oracle leg: changed block without `_ix` names", "fail")
      else ("legacy surgery output: 5 replay, 8 (iii)" ++ routed, "not re-derived")
    rows := rows.push s!"{n.pretty}\t{status}\t{differs}\t{phase}\t{verdict}"
  return rows

/-! ## The command -/

def runValidateLeanCmd (p : Cli.Parsed) : IO UInt32 := do
  let ixe? := (p.flag? "ixe").map (·.as! String)
  let path? : Option String := (p.variableArgsAs! String)[0]?
  if ixe?.isNone && path?.isNone then
    p.printError "error: must specify <path> to a Lean source file (or --ixe <file>)"
    return 1
  match ← Ix.Compile.Pass.switchFromEnv with
    | .ok () => pure ()
    | .error e =>
      p.printError s!"error: {e}"
      return 2
  let skipPhases := ((← IO.getEnv "IX_SKIP_PHASES").getD "").splitOn ","
  let fullOracle := p.hasFlag "full-oracle"
  let mut phases : Array PhaseRow := #[]
  let mut bytes : ByteArray := .empty
  let mut leanEnv? : Option Lean.Environment := none
  -- The regenerated-auxiliary names of the compiled input (path mode).
  let mut inputAux? : Option (Std.HashSet Ix.Name) := none
  -- The names whose block failed to compile (path mode; phase 1 reports them).
  let mut ungrounded : Std.HashSet Ix.Name := {}
  -- Phase 5's decompile oracle, in one of two forms. The default is a
  -- per-name 64-bit DIGEST of the canonicalized source (derived
  -- `Hashable`, same field coverage as the `BEq` used by `--full-oracle`),
  -- collected by the STREAMING compile driver during its transient canon
  -- pass, so the whole-env canon map is never materialized.
  -- `--full-oracle` keeps the old whole-env view: full structural BEq per
  -- constant plus the decompiler's per-recovery debug track — use it to
  -- debug a digest mismatch on a filtered (`--ns`) closure.
  let mut canonView? : Option (Std.HashMap Ix.Name Ix.ConstantInfo) := none
  let mut canonDigests? : Option (Std.HashMap Ix.Name UInt64) := none
  -- Phase 9's cliques: the transported cliques of the compiler's clique
  -- record, read off the compile state at phase 1 (path mode).
  let mut cliques9? : Option (Array (Array Lean.Name)) := none
  IO.println "[validate-lean] mode: Pass 3 (the only mode since M6R slice 6)"

  match ixe?, path? with
  | some ixePath, _ =>
    IO.println s!"Running pure-Lean Ix validator on {ixePath} (no Lean source: phases 1/4 skipped, \
phases 6–8 read Lean's forms from the decompiler)"
    bytes ← IO.FS.readBinFile ixePath
    phases ← pushPhase phases { key := "1", name := "Compile",
                                result := .skipped "pre-compiled .ixe input — no Lean source to compile" }
  | none, some pathStr =>
    IO.println s!"Running pure-Lean Ix validator on {pathStr}"
    unless p.hasFlag "no-build" do buildFile pathStr
    let fe ← getFileEnvCore pathStr
    let leanEnv := fe.env
    leanEnv? := some leanEnv
    let constList ← match p.flag? "ns" with
      | some flag =>
        let raw := flag.as! String
        let prefixes := parsePrefixes raw
        if prefixes.isEmpty then
          IO.println s!"[validate-lean] warning: --ns '{raw}' parsed to empty list; validating full env"
          defaultConstList fe pathStr
        else
          let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
            if prefixes.any (·.isPrefixOf n) then some n else none
          IO.println s!"[validate-lean] filter: {prefixes.length} namespace(s), {seeds.length} seed constants"
          let closed := collectSelectedDeps leanEnv seeds
          IO.println s!"[validate-lean] filter: {closed.length} constants after transitive-dep closure"
          pure closed
      | none =>
        if p.hasFlag "local" then
          -- the file's own constants, with the packing constants of images
          -- and rule statements (a library has them; a closure must too)
          let own := leanEnv.constants.toList.filterMap fun (n, _) =>
            if (leanEnv.getModuleIdxFor? n).isNone then some n else none
          let closed := collectSelectedDeps leanEnv own
          IO.println s!"[validate-lean] local: {own.length} own constants, {closed.length} with their closure"
          pure closed
        else defaultConstList fe pathStr
    inputAux? := some (constList.foldl (init := {}) fun s (n, _) =>
      let ixn := Ix.Name.fromLeanName n
      if Ix.AuxGen.isAuxGenSuffix ixn then s.insert ixn else s)
    IO.println s!"Total constants: {constList.length}"
    IO.println "[validate-lean] phase 1: compiling (pure-Lean pipeline)..."
    (← IO.getStdout).flush
    let compileWorkers := ((p.flag? "workers").map (·.as! Nat)).getD 32
    let t0 ← IO.monoMsNow
    match ← Ix.CompileM.compileLeanConsts constList (numWorkers := compileWorkers) with
    | .error e =>
      phases ← pushPhase phases { key := "1", name := "Compile",
                                  result := .failed s!"pure-Lean pipeline: {e}", ms := (← IO.monoMsNow) - t0 }
    | .ok out =>
      bytes := out.bytes
      cliques9? := some (transportedCliques out.cenv)
      ungrounded := out.cenv.ungrounded.fold (init := {}) fun s n _ => s.insert n
      if fullOracle then
        let constArr := constList.toArray
        let chunkSize := max 1 ((constArr.size + 31) / 32)
        let tasks := (Ix.CanonM.chunks constArr chunkSize).map fun chunk =>
          Task.spawn fun _ => Ix.CanonM.canonChunk chunk
        let mut view : Std.HashMap Ix.Name Ix.ConstantInfo := {}
        for task in tasks do
          for (n, ci) in task.get do
            view := view.insert n ci
        canonView? := some view
      else
        canonDigests? := some out.digests
      let t1 ← IO.monoMsNow
      if out.cenv.ungrounded.size > 0 then
        let shown := out.cenv.ungrounded.toList.take 3
        let msgs := shown.map fun (n, m) => s!"✗ {n.pretty}: {m.take 160}"
        phases ← pushPhase phases { key := "1", name := "Compile", ms := t1 - t0,
                                    result := .failed s!"{out.cenv.ungrounded.size} per-block compile failure(s) \
                                    ({out.bytes.size} bytes)" } msgs.toArray
      else
        phases ← pushPhase phases { key := "1", name := "Compile", ms := t1 - t0,
                                    result := .passed s!"pure-Lean pipeline: {out.bytes.size} bytes, \
                                    {out.blockCount} blocks, {out.ungroundedCount} ungrounded" }
  | none, none => unreachable!

  -- Phase 2: the streaming serde gate.
  IO.println "[validate-lean] phase 2: serde gate (streaming)..."
  (← IO.getStdout).flush
  let t0 ← IO.monoMsNow
  let parts? ← match serdeGateStreaming bytes with
    | .error e =>
      phases ← pushPhase phases { key := "2", name := "Serde", result := .failed e,
                                  ms := (← IO.monoMsNow) - t0 }
      pure none
    | .ok parts =>
      phases ← pushPhase phases { key := "2", name := "Serde", ms := (← IO.monoMsNow) - t0,
                                  result := .passed s!"streaming gate: {parts.env.consts.size} consts / \
                                  {parts.namedRows.size} named rows; writer byte-identical per unit" }
      pure (some parts)
  bytes := .empty
  let pass3Env := match parts? with
    | some parts => parts.namedRows.any fun r => Ix.Compile.Pass.hasReserved r.name
    | none => false
  IO.println s!"[validate-lean] environment: {if pass3Env then "Pass 3 (has `_ix` names)" else "no `_ix` names"}"

  match parts? with
  | none =>
    phases ← pushPhase phases { key := "3", name := "Kernel anon roundtrip", result := .skipped "serde gate failed" }
    phases ← pushPhase phases { key := "4", name := "Kernel meta roundtrip", result := .skipped "serde gate failed" }
  | some parts =>
    -- Phase 3: the anonymous structural roundtrip of every constant.
    -- Memory-diagnosis knobs: `IX_ANON_CAP=<n>` bisects the work list;
    -- `IX_SKIP_PHASES=3,5` skips phases outright.
    if skipPhases.contains "3" then
      phases ← pushPhase phases { key := "3", name := "Kernel anon roundtrip", result := .skipped "IX_SKIP_PHASES" }
    else
      IO.println "[validate-lean] phase 3: kernel anon roundtrip..."
      (← IO.getStdout).flush
      let anonCap := (← IO.getEnv "IX_ANON_CAP").bind (·.toNat?)
      let anonSeq := (← IO.getEnv "IX_ANON_SEQ").isSome
      let anonCut := ((← IO.getEnv "IX_ANON_STAGE").bind (·.toNat?)).getD 0
      let t0 ← IO.monoMsNow
      let (rows, err?) := anonRoundtripEnv parts.env anonCap anonSeq anonCut
      phases ← pushPhase phases { key := "3", name := "Kernel anon roundtrip", ms := (← IO.monoMsNow) - t0,
                                  result := match err? with
                                    | none => .passed s!"{rows} constants structurally preserved"
                                    | some e => .failed s!"after {rows} rows: {e}" }
    -- Phase 4: the meta roundtrip (needs the elaborated env as oracle).
    match leanEnv? with
    | none =>
      phases ← pushPhase phases { key := "4", name := "Kernel meta roundtrip",
                                  result := .skipped "no Lean source env to compare against (--ixe mode)" }
    | some leanEnv =>
      if skipPhases.contains "4" then
        phases ← pushPhase phases { key := "4", name := "Kernel meta roundtrip", result := .skipped "IX_SKIP_PHASES" }
      else
        IO.println "[validate-lean] phase 4: kernel meta roundtrip (streaming)..."
        (← IO.getStdout).flush
        let t0 ← IO.monoMsNow
        let (r, lines) ← phaseMeta leanEnv parts
        phases ← pushPhase phases { key := "4", name := "Kernel meta roundtrip", result := r,
                                    ms := (← IO.monoMsNow) - t0 } lines

  -- The whole environment, materialized once for phases 5–8.
  let ixonEnv? : Option (Except String Ixon.Env) := parts?.map (·.materializeAll)
  -- Path mode: Lean's forms for phases 6–8, read while the Lean environment
  -- is live; the environment is then released before the decompile.
  let mut leanView? : Option View := none
  if let (some leanEnv, some (.ok ixonEnv)) := (leanEnv?, ixonEnv?) then
    let t0 ← IO.monoMsNow
    let v := leanViewOf leanEnv ixonEnv
    IO.println s!"[validate-lean] Lean oracle for phases 6–8: {v.size} constants ({(← IO.monoMsNow) - t0} ms)"
    leanView? := some v
  -- Phase 9 needs Lean's environment: it runs here, while it is live, and
  -- is reported after phase 8.
  let t9 ← IO.monoMsNow
  let (phase9, phase9Lines) : PhaseResult × Array String ← do
    if skipPhases.contains "9" then pure (.skipped "IX_SKIP_PHASES", #[])
    else match leanEnv?, ixonEnv?, leanView?, cliques9? with
      | some leanEnv, some (.ok ixonEnv), some v, some cliques =>
        IO.println s!"[validate-lean] phase 9: clique values ({cliques.size} transported clique(s) in the compiler's clique record)..."
        (← IO.getStdout).flush
        let ixDefs := (changedOf ixonEnv v).cliques.map IxCliqueValues.toLeanName
        -- the record against the `_ix` display members (log only): record cliques
        -- with no `_ix` definition display member, and display members of no
        -- record clique (the O7–O12 forms)
        let inRecord : Std.HashSet Lean.Name := cliques.foldl (fun s c => c.foldl (·.insert ·) s) {}
        let ixSet : Std.HashSet Lean.Name := ixDefs.foldl (·.insert ·) {}
        let bare := cliques.filter fun c => !c.any ixSet.contains
        let outside := ixDefs.filter (!inRecord.contains ·)
        IO.println s!"[validate-lean] phase 9: record vs `_ix` display members: {bare.size} record clique(s) \
          without one {(bare.toList.take 8).map (·.toList)}; {outside.size} display member(s) of no record clique \
          {(outside.toList.take 8)}"
        phaseCliqueValues leanEnv ixonEnv cliques ixDefs.size
      | none, _, _, _ =>
        pure (.skipped "no Lean source environment (--ixe mode): phase 9 evaluates Lean's constants", #[])
      | _, _, _, none => pure (.skipped "no compile state (phase 1 failed): no clique record", #[])
      | _, _, _, _ => pure (.skipped "no materialized environment", #[])
  let ms9 := (← IO.monoMsNow) - t9
  leanEnv? := none

  -- Phase 5: decompile through the full pure-Lean driver.
  let mut decompiled? : Option View := none
  match ixonEnv? with
  | none =>
    phases ← pushPhase phases { key := "5", name := "Decompile", result := .skipped "serde gate failed" }
  | some (.error e) =>
    phases ← pushPhase phases { key := "5", name := "Decompile", result := .failed s!"named metadata materialization: {e}" }
  | some (.ok ixonEnv) =>
    if skipPhases.contains "5" then
      phases ← pushPhase phases { key := "5", name := "Decompile", result := .skipped "IX_SKIP_PHASES" }
    else
      IO.println "[validate-lean] phase 5: decompiling (full driver)..."
      (← IO.getStdout).flush
      let t0 ← IO.monoMsNow
      let decompileWorkers := ((p.flag? "workers").map (·.as! Nat)).getD 16
      let (decompiled, errs, _p2st) ←
        Ix.DecompileM.decompileEnvFullParallel ixonEnv canonView? (numWorkers := decompileWorkers)
      decompiled? := some decompiled
      let t1 ← IO.monoMsNow
      let nRecords := ixonEnv.named.fold (init := 0) fun k _ nd =>
        if (metaHasAlteringSurgery nd.constMeta) then k + 1 else k
      let scope := s!"{nRecords} constant(s) with call-site or `_ix.inline` records replayed"
      let (r, lines) : PhaseResult × Array String := Id.run do
        if !errs.isEmpty then
          let msgs := (errs.extract 0 5).map fun (n, m) => s!"✗ {n.pretty}: {m.take 160}"
          return (.failed s!"{errs.size} decompile error(s) ({decompiled.size} constants)", msgs)
        let compare (sameAs : Ix.Name → Ix.ConstantInfo → Option Bool) (names : Array Ix.Name) :
            Nat × Array Ix.Name × Nat := Id.run do
          let mut nMatch := 0
          let mut mismatches : Array Ix.Name := #[]
          let mut missing := 0
          for (name, info) in decompiled do
            match sameAs name info with
            | some true => nMatch := nMatch + 1
            | some false => mismatches := mismatches.push name
            | none => missing := missing + 1
          for name in names do
            if !decompiled.contains name then
              missing := missing + 1
              mismatches := mismatches.push name
          return (nMatch, mismatches, missing)
        match canonView?, canonDigests? with
        | some view, _ =>
          let (m, mis, missing) := compare (fun n ci => (view.get? n).map (· == ci))
            (view.toArray.map (·.1))
          if mis.isEmpty && missing == 0 then
            return (.passed s!"{m} constants reconstructed hash-identical to the canonicalized source; {scope}", #[])
          return (.failed s!"{mis.size} mismatch(es), {missing} missing; {m} matched; {scope}",
            (mis.extract 0 8).map (s!"✗ {·.pretty}"))
        | none, some digs =>
          let (m, mis, missing) := compare (fun n ci => (digs.get? n).map (· == hash ci))
            (digs.toArray.map (·.1))
          if mis.isEmpty && missing == 0 then
            return (.passed s!"{m} constants reconstructed digest-identical to the canonicalized source; {scope}", #[])
          return (.failed s!"{mis.size} digest mismatch(es), {missing} missing; {m} matched; {scope} \
— rerun with --full-oracle --ns <namespace> for a structural diff",
            (mis.extract 0 8).map (s!"✗ {·.pretty}"))
        | none, none =>
          return (.passed s!"oracle-free: {decompiled.size} constants decompiled, 0 errors; {scope}", #[])
      phases ← pushPhase phases { key := "5", name := "Decompile", result := r, ms := t1 - t0 } lines

  -- Phases 6–8 over the materialized environment and Lean's forms.
  let names678 := [("6", "Oracle leg (unchanged blocks)"), ("7", "Image rules (changed blocks)"),
    ("8", "Provenance")]
  match ixonEnv? with
  | some (.ok ixonEnv) =>
    let view? : Option (View × String) := match leanView?, decompiled? with
      | some v, _ => some (v, "Lean source")
      | none, some d => some (d, "decompiled")
      | none, none => none
    match view? with
    | none =>
      for (k, n) in names678 do
        phases ← pushPhase phases { key := k, name := n,
                                    result := .skipped "no oracle for Lean's forms (phase 5 skipped in --ixe mode)" }
    | some (view, oracleName) =>
      let limits ← match ← Ix.CompileM.compilerSharingLimitsFromEnv with
        | .ok l => pure l
        | .error e => throw (IO.userError s!"validate-lean: {e}")
      let ch := changedOf ixonEnv view
      let mut rulesProblems : Array String := #[]
      -- one recompile of Lean's forms serves phases 6 and 8
      let t0 ← IO.monoMsNow
      let needed := ixonEnv.named.fold (init := #[]) fun acc n nd =>
        if nd.original.isSome && !Ix.Compile.Pass.hasReserved n then acc.push n else acc
      let rc := if skipPhases.contains "6" && skipPhases.contains "8" then {}
        else recompileAll (cenvOver ixonEnv view limits) view needed
      let tRc := (← IO.monoMsNow) - t0
      IO.println s!"[validate-lean] Lean forms recompiled for phases 6 and 8: {rc.units} units, \
{rc.addrs.size} names ({tRc} ms; oracle: {oracleName})"
      if skipPhases.contains "6" then
        phases ← pushPhase phases { key := "6", name := "Oracle leg (unchanged blocks)", result := .skipped "IX_SKIP_PHASES" }
      else
        let t0 ← IO.monoMsNow
        let (r, lines) := phaseOracle ixonEnv view ch rc inputAux? ungrounded
          (pass3 := inputAux?.isSome || pass3Env)
          (explain := (← IO.getEnv "IX_VALIDATE_EXPLAIN").isSome)
        phases ← pushPhase phases { key := "6", name := "Oracle leg (unchanged blocks)", result := r,
                                    ms := (← IO.monoMsNow) - t0 + tRc } lines
      if skipPhases.contains "7" then
        phases ← pushPhase phases { key := "7", name := "Image rules (changed blocks)", result := .skipped "IX_SKIP_PHASES" }
      else
        let t0 ← IO.monoMsNow
        let (r, lines, probs) := phaseRules ixonEnv view ch limits ungrounded
        rulesProblems := probs
        phases ← pushPhase phases { key := "7", name := "Image rules (changed blocks)", result := r,
                                    ms := (← IO.monoMsNow) - t0 } lines
      if skipPhases.contains "8" then
        phases ← pushPhase phases { key := "8", name := "Provenance", result := .skipped "IX_SKIP_PHASES" }
      else
        let t0 ← IO.monoMsNow
        let (r, lines) := phaseProvenance ixonEnv view ch rc
        phases ← pushPhase phases { key := "8", name := "Provenance", result := r,
                                    ms := (← IO.monoMsNow) - t0 } lines
      if let some path := ← IO.getEnv "IX_VALIDATE_AUXTABLE" then
        let rows := auxTableRows ixonEnv view ch rc rulesProblems
          (inputAux?.isSome || pass3Env)
        IO.FS.writeFile path ("\n".intercalate rows.toList ++ "\n")
        IO.println s!"[validate-lean] auxiliary table: {rows.size - 1} row(s) to {path}"
  | _ =>
    for (k, n) in names678 do
      phases ← pushPhase phases { key := k, name := n, result := .skipped "no materialized environment" }
  phases ← pushPhase phases { key := "9", name := "Clique values", result := phase9, ms := ms9 } phase9Lines

  -- The summary table, then a `RESULT:` line matching `ix validate`'s.
  IO.println ""
  IO.println s!"[validate-lean] phase summary (\
{if pass3Env then "Pass 3 environment" else "no `_ix` names"}):"
  IO.println "[validate-lean]   #  phase                          verdict  time"
  for r in phases do
    let name := r.name.pushn ' ' (30 - min 30 r.name.length)
    let secs := s!"{r.ms / 1000}.{(r.ms % 1000) / 100} s"
    IO.println s!"[validate-lean]   {r.key}  {name} {r.result.tag}     {secs}"
  for r in phases do
    IO.println s!"[validate-lean]   {r.key}. {r.name}: {r.result.render}"
  IO.println s!"[validate-lean] VERDICTS {" ".intercalate (phases.toList.map fun r => s!"{r.key}={r.result.tag}")}"
  let failures := phases.filter (·.result.isFailure)
  IO.println s!"[validate-lean] RESULT: {failures.size} total failures"
  (← IO.getStdout).flush

  -- `--report`: machine-readable phase table + verdict.
  if let some flag := p.flag? "report" then
    let phaseRows := Lean.Json.arr <| phases.map fun r =>
      let (result, detail) := match r.result with
        | .passed d => ("pass", d)
        | .failed d => ("fail", d)
        | .stubbed d => ("stub", d)
        | .skipped d => ("skip", d)
      Lean.Json.mkObj
        [ ("key", Lean.Json.str r.key)
        , ("name", Lean.Json.str r.name)
        , ("result", Lean.Json.str result)
        , ("detail", Lean.Json.str detail)
        , ("ms", Lean.toJson r.ms) ]
    let report := Lean.Json.mkObj
      [ ("schemaVersion", Lean.toJson (2 : Nat))
      , ("tool", Lean.Json.str "validate-lean")
      , ("ixVersion", Lean.Json.str Ix.versionString)
      , ("leanToolchain", Lean.Json.str Lean.versionString)
      , ("input", Lean.Json.str (ixe?.getD (path?.getD "")))
      , ("ns", (p.flag? "ns").map (Lean.Json.str <| ·.as! String) |>.getD Lean.Json.null)
      , ("local", Lean.toJson (p.hasFlag "local"))
      , ("pass3Switch", Lean.toJson true)
      , ("pass3Env", Lean.toJson pass3Env)
      , ("phases", phaseRows)
      , ("totalFailures", Lean.toJson failures.size)
      , ("passed", Lean.toJson failures.isEmpty) ]
    IO.FS.writeFile (flag.as! String) (report.pretty ++ "\n")

  return if failures.isEmpty then 0 else 1

end Ix.Cli.ValidateLeanCmd

open Ix.Cli.ValidateLeanCmd in
def validateLeanCmd : Cli.Cmd := `[Cli|
  "validate-lean" VIA runValidateLeanCmd;
  "Validate a Lean file through the pure-Lean Ix pipeline: compile, serde, kernel roundtrips (anon, meta), decompile, oracle leg, image rules, provenance, clique values (the Phase A validator of record)"

  FLAGS:
    ns  : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are validated; transitive deps (with the recursors of every inductive) are pulled in automatically."
    "local"; "Validate only the constants the file itself declares, with their closure and the constants images and rule statements are built from (PProd, And, True, Eq), as `aux-cert` does."
    "no-build"; "Skip the Lake build of the input module (the caller has built it and its imports, e.g. a suite that builds every fixture in one `lake build`). The file is still elaborated."
    ixe : String; "Validate a pre-compiled .ixe instead of a Lean file (no Lean source: phases 1 and 4 skipped, phases 6-8 read Lean's forms from the decompiler)"
    report : String; "Write a machine-readable JSON report (phase table + pass/fail) to this path."
    workers : Nat; "Worker count for the parallel phases (compile phase 1, decompile phase 5); default 32 for compile, 16 for decompile. Lower at whole-Mathlib scale: memory scales with workers."
    "full-oracle"; "Phase 5 comparison via the full canonicalized env (structural BEq per constant + the decompiler's per-recovery debug track) instead of the default per-name digests. Use on --ns-filtered closures to debug a digest mismatch."

  ARGS:
    ...path : String; "Path to the Lean source file whose env should be validated (omit with --ixe)."
]

end
