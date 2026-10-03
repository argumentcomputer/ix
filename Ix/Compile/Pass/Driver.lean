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
   (`Ix.Compile.Pass.Translate`, Def 3.6) into an environment overlay, the
   source occurrences become the block's decompile records, and the image
   constant of every bare or partial occurrence (`a._ix`, Q11) is compiled as
   an ordinary constant and stored with the block (its `Named.original`, the
   provenance of Lean's `a`, is filled in at assembly).

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
  let kept : Std.HashSet Name := heads.foldl (·.insert ·) {}
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
  let name := imageName a
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

/-- Rewrite a block before it compiles: the compile environment (overlay,
decompile sources) and the initial block state (stored image constants).
Identity when the switch is off or the block references no head. -/
def prepareBlock (cenv : CompileEnv) (all : Set Name) (lo : Name) :
    Except String (CompileEnv × BlockState) := do
  if !cenv.pass3 || cenv.p3Heads.isEmpty then return (cenv, {})
  if let some refs := cenv.p3BlockRefs.get? lo then
    if !refs.toList.any cenv.p3Heads.contains then return (cenv, {})
  let mut members : Array (Name × ConstantInfo) := #[]
  let mut used : Std.HashSet Name := {}
  for n in all do
    if let some ci := cenv.env.get? n then
      members := members.push (n, ci)
      used := (headsIn cenv.p3Heads ci).fold (·.insert ·) used
  if used.isEmpty then return (cenv, {})
  -- the views of the referenced changed blocks
  let mut views : Std.HashMap Name BlockView := {}
  for h in used do
    if let some key := cenv.p3Heads.get? h then
      if !views.contains key then
        views := views.insert key (← viewOf cenv views key)
  let lookup := expansionLookup cenv views
  let rwr ← rewriteBlock lookup members
  -- image constants of bare and partial occurrences, dependencies first
  let mut known : Std.HashMap Name Address := {}
  let mut init : BlockState := {}
  let mut pending := rwr.needed
  let mut fuel := 4 * (pending.size + 1) * (cenv.p3Heads.size + 1)
  while !pending.isEmpty do
    if fuel == 0 then throw "Pass 3: image constants have cyclic dependencies"
    fuel := fuel - 1
    let a := pending[0]!
    pending := pending.extract 1 pending.size
    let name := imageName a
    if known.contains name then continue
    let (dv, needed) ← imageDecl cenv views a
    let missing := needed.filter fun b => !known.contains (imageName b)
    if !missing.isEmpty then
      pending := missing ++ #[a] ++ pending
      continue
    let (r, bs) ← compileImage cenv known dv
    known := known.insert name r.blockAddr
    init := { init with
      blockNameToAddr := init.blockNameToAddr.insert name r.blockAddr
      auxConsts := init.auxConsts.push (r.blockAddr, r.block)
      auxNamed := init.auxNamed.push (name, { addr := r.blockAddr, constMeta := r.blockMeta })
      auxNameToAddr := init.auxNameToAddr.insert name r.blockAddr
      blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) init.blockBlobs
      blockNames := bs.blockNames.fold (fun m k v => m.insert k v) init.blockNames
      defHints := bs.defHints.fold (fun m k v => m.insert k v) init.defHints }
  let overlay : Std.HashMap Name ConstantInfo :=
    rwr.overlay.foldl (fun m (n, ci) => m.insert n ci) {}
  let sources : Std.HashMap Nat Expr :=
    rwr.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) {}
  return ({ cenv with env := { cenv.env with overlay }, p3Sources := sources }, init)

/-! ## Assembly -/

/-- Give every stored image constant `a._ix` the provenance of Lean's `a`
(`Named.original`), once the promotion pass has computed it. -/
def fillImageOriginals (named : Std.HashMap Name Ixon.Named) (images : Array Name) :
    Std.HashMap Name Ixon.Named := Id.run do
  let mut out := named
  for a in images do
    if let some img := out.get? (imageName a) then
      if let some orig := (out.get? a).bind (·.original) then
        out := out.insert (imageName a) { img with original := some orig }
  return out

end Ix.Compile.Pass

end
