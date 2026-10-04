/- # Pass 3 in the compile fold (the switch `IX_PASS3=images`)

## Contract
Two hooks of the block compile (`Ix.CompileDriver`), both inert unless
`CompileEnv.pass3`:

1. **After the aux tail of a changed block** (`editChangedBlock`): the block
   is changed when today's plan predicate holds (fewer classes than Lean's
   `all`, a class representative out of `all` order, or a nested auxiliary
   moved or evaporated), which under the compiler's rules is Def 3.1. No
   surgery plan is registered. The side-car edit (`Ix.Compile.Pass.SideCar`)
   gives every Ix auxiliary its `_ix` display name and moves the canonical
   `IndPredBelow` family off Lean's names; the block records its image-kind
   heads, its Lean `all` and Pass 2's canonical recursors for the driver.
2. **Before a block compiles** (`prepareBlock`): when the block references
   an image-kind head of a changed block, its members are rewritten
   (`Ix.Compile.Pass.Translate`, Def 3.6) into an environment overlay (the
   definitional passes, `Ix.Compile.Pass.Opt.Engine`, are tried first at every
   full application: `optLookup`, the one A4 call site), the
   source occurrences become the block's decompile records, and the image
   constant of every bare or partial occurrence (`a._ix`, Q11) is compiled as
   an ordinary constant and stored with the block (its `Named.original`, the
   provenance of Lean's `a`, is filled in at assembly).

   The changed-clique hook (`Ix.Compile.Pass.Cliques.prepareCliques`, A5)
   runs first, at this one call site: the members of a changed definition
   clique and their carried equation lemmas get their transported values in
   the overlay (with Lean's values as decompile records, placeholder indices
   from `cliqueRecordBase`), and the canonical `_ix` constants they reach are
   compiled into the block; the call-site rewrite then applies to the
   overlay as to any member.

## Faithfulness
See `Translate` (the rewrite is definitional) and `ImageView` (images compute
as Lean's recursors). The originals of the regenerated auxiliaries are still
compiled for `Named.original` by the promotion pass, now with no call-site
rewrite at all (no plan exists): the provenance is Lean's form as written.

## Canonicity
Faithful only (A4's definitional passes restore the optimised forms).
Identity blocks are untouched: every byte of a compile with no changed block
is the switch-off output.

## Side condition and fallback
A failure to build an image or to rewrite is a compile error of the block
that needs it, naming the constant (no fallback to surgery under the
switch).

## Non-canonical set and evidence
`BARE` for stored image constants. Evidence: the `pass3` suite.
-/
module
public import Ix.CompileM
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Translate
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.SideCar
public import Ix.Compile.Pass.Opt.Engine
public import Ix.Compile.Pass.Cliques
public section

namespace Ix.Compile.Pass

open Ix (Name Expr ConstantInfo)
open Ix.CompileM

/-- `stt.resolve_addr` over a compile environment. -/
def resolveAddr (cenv : CompileEnv) (n : Name) : Option Address :=
  match cenv.nameToAddr.get? n with
  | some a => some a
  | none => cenv.auxNameToAddr.get? n

/-- `AuxLayout.perm`'s out-of-component marker (`PERM_OUT_OF_SCC`). -/
def permOut : UInt64 := 0xFFFFFFFFFFFFFFFF

/-! ## Hook 1: after the aux tail -/

/-- The Lean `all` of a block's inductives. -/
def leanAllOf (cs : Array MutConst) : Array Name := Id.run do
  for c in cs do
    if let .indc ind := c then return ind.all
  return #[]

/-- Today's plan predicate (`compileMutualAuxTail`), which is Def 3.1 under
the compiler's rules. -/
def isChanged (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Bool :=
  let originalAll := leanAllOf cs
  let lookup : Std.HashSet Name := originalAll.foldl (init := {}) (·.insert ·)
  let planClasses := classNames.filterMap fun cls =>
    let ns := cls.filter lookup.contains
    if ns.isEmpty then none else some ns
  let userChanged := !originalAll.isEmpty
    && (planClasses.size < originalAll.size
      || (planClasses.size == originalAll.size
        && (planClasses.zip originalAll).any fun (cls, orig) => cls[0]! != orig))
  let auxChanged := match layout? with
    | some l => l.evaporated.any (· != 0)
        || l.perm.zipIdx.any fun (i, j) => i != permOut && i.toNat != j
    | none => false
  userChanged || auxChanged

/-- The side-car edit and the driver records of a changed block, applied to
the block state. -/
def editChangedBlock (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : CompileM Unit := do
  let cenv ← getCompileEnv
  let originalAll := leanAllOf cs
  let some all0 := originalAll[0]? | return
  let lookup : Std.HashSet Name := originalAll.foldl (init := {}) (·.insert ·)
  let planClasses := classNames.filterMap fun cls =>
    let ns := cls.filter lookup.contains
    if ns.isEmpty then none else some ns
  let some rep0 := (planClasses[0]?).bind (·[0]?) | return
  let perm : Array (Option Nat) := match layout? with
    | some l => l.perm.map fun p => if p == permOut then none else some p.toNat
    | none => #[]
  let heads := imageKinds cenv.env.get? originalAll
  -- every Lean name moves off the Ix auxiliaries: the image kinds denote
  -- their stored images (compiled when their own block comes up,
  -- `compileImageBlock`), the rest are Lean's own blocks
  let kept : Std.HashSet Name := {}
  let st ← getBlockState
  let mut display : Std.HashMap Name Name := {}
  for n in st.auxNamed.map (·.1) ++ st.auxNameToAddr.toArray.map (·.1) do
    if display.contains n then continue
    if let some d := ixAuxName originalAll rep0 perm n then
      display := display.insert n d
  let edit : SideCarEdit := { display, kept }
  let (named, n2a, extra) := edit.apply st.auxNamed st.auxNameToAddr st.auxGenExtraNames
  for (_, d) in display do compileName d
  modifyBlockState fun st => { st with
    auxNamed := named, auxNameToAddr := n2a, auxGenExtraNames := extra
    p3Heads := st.p3Heads ++ heads.map (·, all0)
    p3Blocks := st.p3Blocks.push (all0, originalAll) }

/-! ## Hook 2: before a block compiles -/

/-- The heads a constant mentions. A walk over distinct nodes. -/
def headsIn (heads : Std.HashMap Name Name) (ci : ConstantInfo) : Std.HashSet Name := Id.run do
  let mut roots : Array Expr := #[ci.getCnst.type]
  match ci with
  | .defnInfo v => roots := roots.push v.value
  | .thmInfo v => roots := roots.push v.value
  | .opaqueInfo v => roots := roots.push v.value
  | .recInfo v => roots := roots ++ v.rules.map (·.rhs)
  | _ => pure ()
  let mut seen : Std.HashSet Expr := {}
  let mut out : Std.HashSet Name := {}
  let mut stack := roots
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ _ => if heads.contains n then out := out.insert n
    | .app f a _ => stack := stack.push a |>.push f
    | .lam _ t b _ _ | .forallE _ t b _ _ => stack := stack.push b |>.push t
    | .letE _ t v b _ _ => stack := stack.push b |>.push v |>.push t
    | .proj _ _ s _ | .mdata _ s _ => stack := stack.push s
    | _ => pure ()
  return out

/-- The view input of a compile environment. -/
def viewInput (cenv : CompileEnv) : ViewInput :=
  { const? := cenv.env.get?, addr? := resolveAddr cenv, canonRec? := cenv.p3CanonRecs.get? }

/-- The view of the changed Lean block `key`. -/
def viewOf (cenv : CompileEnv) (views : Std.HashMap Name BlockView) (key : Name) :
    Except String BlockView :=
  match views.get? key with
  | some v => pure v
  | none => buildView (viewInput cenv) ((cenv.p3Blocks.get? key).getD #[key])

/-- The expansion lookup of a block, with the views of the given Lean blocks
precomputed (others are built on demand). -/
def expansionLookup (cenv : CompileEnv) (views : Std.HashMap Name BlockView) :
    Name → Except String (Option Expansion) := fun n =>
  match cenv.p3Heads.get? n with
  | none => pure none
  | some key => do
    let v ← viewOf cenv views key
    let (x, _) ← v.expansion (viewInput cenv) n
    return some x

/-- The image constant `a._ix` of a needed head (a bare or partial
occurrence) as an ordinary definition, with the heads its rewritten value
needs in turn. -/
def imageDecl (cenv : CompileEnv) (views : Std.HashMap Name BlockView) (a : Name) :
    Except String (Ix.DefinitionVal × Array Name) := do
  let some key := cenv.p3Heads.get? a | throw s!"Pass 3: {a.pretty} is not an image-kind head"
  let inp := viewInput cenv
  let v ← viewOf cenv views key
  let (x, ty) ← v.expansion inp a
  let lookup := expansionLookup cenv views
  -- the value (and the type) with every head rewritten, no records
  let rwM : RwM (Expr × Expr) := do
    let x' ← if x.needsRewrite then rw lookup rewriteFuel false x.value else pure x.value
    let ty' ← rw lookup rewriteFuel false ty
    pure (x', ty')
  let ((value, type), st) ← rwM.run { base := 0 }
  let safety : Lean.DefinitionSafety := match inp.const? a with
    | some (.defnInfo d) => d.safety
    | some (.recInfo r) => if r.isUnsafe then .unsafe else .safe
    | _ => .safe
  let name := a
  return ({ cnst := { name, levelParams := x.levelParams, type }
            value, hints := .abbrev, safety, all := #[name] }, st.needed.filter (· != a))

/-- Compile an image constant; `known` resolves the block's earlier images. -/
def compileImage (cenv : CompileEnv) (known : Std.HashMap Name Address)
    (dv : Ix.DefinitionVal) : Except String (BlockResult × BlockState) := do
  let name := dv.cnst.name
  let blockEnv : BlockEnv := { all := ({} : Ix.Set Name).insert name, current := name,
                               mutCtx := default, univCtx := [] }
  let init : BlockState := { blockNameToAddr := known }
  match CompileM.run cenv blockEnv init (compileConstantInfo (.defnInfo dv)) with
  | .ok (r, bs) => return (r, bs)
  | .error e => throw s!"Pass 3: image constant {name.pretty}: {e}"

/-- The definitional passes (`Ix.Compile.Pass.Opt.engine`) over the views of a
block's referenced changed blocks: the hook the rewrite tries at every full
application before it inlines an image (heads of other blocks keep their
baseline). -/
def optLookup (cenv : CompileEnv) (views : Std.HashMap Name BlockView) :
    Name → Array Ix.Level → Array Expr → Option Expr :=
  let inp := viewInput cenv
  let blocks : Std.HashMap Name Opt.OptBlock :=
    views.fold (fun m k v => m.insert k (Opt.optBlockOf inp v)) {}
  let env : Opt.OptEnv :=
    { ienv := cenv.env, resolves := fun n => (resolveAddr cenv n).isSome
      blockOf := fun h => (cenv.p3Heads.get? h).bind blocks.get? }
  fun n us args => (Opt.engine env { head := n, us, args }).map (·.2)

/-- Pass 3's rewrite of a changed clique's canonical constants (the clique
hook's `rewrite`): the views of the changed blocks they reference, then the
call-site rewrite with the definitional passes (`optLookup`), exactly as for
the constants of any block. Without the views the passes see no block and
every full application would keep its inlined image. -/
def cliqueRewrite (cenv : CompileEnv) (members : Array (Name × ConstantInfo)) :
    Except String BlockRewrite := do
  let mut views : Std.HashMap Name BlockView := {}
  for (_, ci) in members do
    for h in headsIn cenv.p3Heads ci do
      if let some key := cenv.p3Heads.get? h then
        if !views.contains key then views := views.insert key (← viewOf cenv views key)
  rewriteBlock (expansionLookup cenv views) members (optLookup cenv views)

/-- Rewrite a block before it compiles: the compile environment (overlay,
decompile sources) and the initial block state (stored image constants).
Identity when the switch is off or the block references no head. -/
def prepareBlock (cenv : CompileEnv) (all : Set Name) (lo : Name) :
    Except String (CompileEnv × BlockState) := do
  if !cenv.pass3 then return (cenv, {})
  -- changed definition cliques (`Ix.Compile.Pass.Cliques`, the A5 hook): the
  -- members' transported values with their decompile records, and the
  -- canonical constants they reference
  let (cenv, init) ← prepareCliques cenv all (cliqueRewrite cenv)
  if cenv.p3Heads.isEmpty then return (cenv, init)
  if let some refs := cenv.p3BlockRefs.get? lo then
    if !refs.toList.any cenv.p3Heads.contains then return (cenv, init)
  let mut members : Array (Name × ConstantInfo) := #[]
  let mut used : Std.HashSet Name := {}
  for n in all do
    if let some ci := cenv.env.get? n then
      members := members.push (n, ci)
      used := (headsIn cenv.p3Heads ci).fold (·.insert ·) used
  if used.isEmpty then return (cenv, init)
  -- the views of the referenced changed blocks
  let mut views : Std.HashMap Name BlockView := {}
  for h in used do
    if let some key := cenv.p3Heads.get? h then
      if !views.contains key then
        views := views.insert key (← viewOf cenv views key)
  let lookup := expansionLookup cenv views
  let rwr ← rewriteBlock lookup members (optLookup cenv views)
  let overlay : Std.HashMap Name ConstantInfo :=
    rwr.overlay.foldl (fun m (n, ci) => m.insert n ci) cenv.env.overlay
  let sources : Std.HashMap Nat Expr :=
    rwr.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) cenv.p3Sources
  return ({ cenv with env := { cenv.env with overlay }, p3Sources := sources }, init)

/-! ## The Lean names of a changed block's auxiliaries: their images -/

/-- Every member of the block is an image-kind auxiliary of a changed block
(its recursors, or `casesOn`/`recOn`/`below*`/`brecOn*`): the block compiles
to their images. -/
def isImageBlock (cenv : CompileEnv) (all : Set Name) : Bool :=
  cenv.pass3 && !all.isEmpty && all.toList.all cenv.p3Heads.contains

/-- Compile the images of an image block, each an ordinary definition under
the Lean name (the name map sends a changed block's auxiliary to its image,
the constant with Lean's type). Members are compiled in an order in which
each resolves the ones before it (`known`). -/
def compileImageBlock (cenv : CompileEnv) (all : Set Name) :
    Except String (Array (Name × BlockResult × BlockState)) := do
  let mut views : Std.HashMap Name BlockView := {}
  for a in all do
    if let some key := cenv.p3Heads.get? a then
      if !views.contains key then views := views.insert key (← viewOf cenv views key)
  let mut pending := all.toArray.qsort (fun a b => a.pretty < b.pretty)
  let mut known : Std.HashMap Name Address := {}
  let mut out : Array (Name × BlockResult × BlockState) := #[]
  let mut lastErr := ""
  let mut rounds := pending.size + 1
  while !pending.isEmpty && rounds > 0 do
    rounds := rounds - 1
    let mut rest : Array Name := #[]
    for a in pending do
      let (dv, _) ← imageDecl cenv views a
      match compileImage cenv known dv with
      | .ok (r, bs) =>
        known := known.insert a r.blockAddr
        out := out.push (a, r, bs)
      | .error e =>
        lastErr := e
        rest := rest.push a
    pending := rest
  if !pending.isEmpty then throw lastErr
  return out



end Ix.Compile.Pass

end
