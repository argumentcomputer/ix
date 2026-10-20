/- # Pass 3 in the compile fold

## Contract
Two hooks of the block compile (`Ix.CompileDriver`), always on, and the
compile of image blocks. Each hook **returns** what the block publishes
(`Published`); the driver checks it against the live state and merges it
(`checkBlockClaims`, `mergeCompiledBlock`). Nothing is accumulated in
`BlockState` (R07-06b).

1. **After the aux tail** (`editBlock`). A block is *changed* when the
   change predicate holds (`Ix.Compile.ChangedSet.isChanged`: fewer classes
   than Lean's `all`, a class representative out of `all` order, or a nested
   auxiliary moved or evaporated; Def 3.1 under the compiler's rules). For a
   changed block (`editChangedBlock`) the side-car edit
   (`Ix.Compile.Pass.SideCar`) moves every registration the tail made under a
   Lean name to its `_ix` display name (`ixAuxName`), and the block publishes
   its image-kind heads (`sourceImageHeads`: `imageKinds` that source
   recognition admits), its Lean `all` and Pass 2's canonical recursors. An
   unchanged block whose Lean `IndPredBelow` family is stored permuted is
   treated as a changed block whose members are the family's `below`
   inductives (`editPermutedBelowFamily`, A3V-IPB).
2. **Before a block compiles** (`prepareBlock`). When the block's members
   reference an image-kind head, they are rewritten (`Translate`, Def 3.6)
   into an environment overlay; every outermost rewritten call site carries
   a placeholder whose source occurrence goes to `CompileEnv.p3Sources`, and
   `Ix.CompileM.compileExprWithRecords` compiles it into the constant's
   `_ix.inline` decompile record (meta mode: metadata only). A bare or
   partial occurrence keeps the Lean name, which denotes the stored image.
3. **Image blocks** (`isImageBlock`, `runImageBlock`). A block every member
   of which is an image-kind head compiles to the images under the Lean
   names, each of Lean's kind (a theorem for a Lean theorem), with
   `Named.original` = Lean's own form compiled without the aux tail.

A changed block's heads are published by its merge, in its wave; every
block that reads them (a caller, an image block) depends on the head's own
block, which depends on the changed block, so it compiles in a later wave
and reads them from its wave's snapshot.

## Faithfulness
See `Translate` (the rewrite is definitional) and `ImageView` (images compute
as Lean's recursors). Source definitions compile from their own bodies; a
user-written `X.casesOn`/`X.recOn`/`X.below`/`X.brecOn` is a head only when
source recognition identifies it with the generated one
(`Ix.AuxGen.SourceIdentity`, `Ix.AuxGen.SourceFamily`).

## Canonicity
Faithful only: no definitional pass, no clique transport and no
proof-justified form (batch 5). The non-canonical set stays empty.

## Side condition and fallback
A failure to build an image or to rewrite is a compile error of the block
that needs it, naming the constant (no fallback).

## Shape (for the statements)
Every function here is total: folds over arrays and maps, the view and the
rewrite of `ImageView` and `Translate` (explicit bounds), and `CompileM`
runs. The memo tables (`CompileEnv.p3Views`, `p3ImageExps`) only store
values the computation gives (`Ix.Compile.Pass.MemoSound`).
-/
module
public import Ix.CompileM
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.Memo
public import Ix.Compile.Pass.Translate
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.SideCar
public import Ix.Compile.ChangedSet.Block
public import Ix.AuxGen.SourceIdentity
public import Ix.AuxGen.SourceFamily
public section

namespace Ix.Compile.Pass

open Ix (Name Expr ConstantInfo RecursorVal MutConst)
open Ix.CompileM
open Ix.Compile.ExactKey (ExactName nameEq)

/-- What one block publishes for Pass 3, returned by the hooks and merged by
the driver (insert-once, `Ix.CompileM.checkBlockClaims`). -/
structure Published where
  /-- Image-kind head ↦ its changed block's key (Lean's first member). -/
  heads : Array (Name × Name) := #[]
  /-- Changed block's key ↦ its Lean `all`. -/
  blocks : Array (Name × Array Name) := #[]
  /-- Pass 2's canonical recursors of a changed block, by aux-gen's names. -/
  canonRecs : Array (Name × RecursorVal) := #[]
  /-- New entries of the view memo (`CompileEnv.p3Views`). -/
  views : Array (Name × BlockView) := #[]
  /-- New entries of the image memo (`CompileEnv.p3ImageExps`): recursor images,
  and definitional heads' rewritten expansions (`compileImageBlock`). -/
  imageExps : Array (Name × (Expansion × Expr)) := #[]
  deriving Inhabited

instance : Append Published where
  append a b := { heads := a.heads ++ b.heads, blocks := a.blocks ++ b.blocks
                  canonRecs := a.canonRecs ++ b.canonRecs, views := a.views ++ b.views
                  imageExps := a.imageExps ++ b.imageExps }

/-- `stt.resolve_addr` over a compile environment: `nameToAddr`, then
`auxNameToAddr`. -/
def resolveAddr (cenv : CompileEnv) (n : Name) : Option Address :=
  match cenv.nameToAddr.get? n with
  | some a => some a
  | none => cenv.auxNameToAddr.get? n

/-! ## Hook 1: after the aux tail -/

/-- The Lean `all` of a block's inductives (`#[]` for a block without one). -/
def leanAllOf (cs : Array MutConst) : Array Name := Id.run do
  for c in cs do
    if let .indc ind := c then return ind.all
  return #[]

/-- The display-name inputs of a component (`ixAuxName`): Lean's `all`, the
first class representative among `all`'s members, the nested source
permutation (`none` for a position out of the component). -/
def displayInputs (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Option (Array Name × Name × Array (Option Nat)) := do
  let originalAll := leanAllOf cs
  let rep0 ← ((Ix.Compile.ChangedSet.planClasses originalAll classNames)[0]?).bind (·[0]?)
  let perm : Array (Option Nat) := match layout? with
    | some l => l.perm.map fun p =>
        if p == Ix.Compile.ChangedSet.permOut then none else some p.toNat
    | none => #[]
  return (originalAll, rep0, perm)

/-- Move the tail's registrations selected by `sel` to their display names
(`SideCarEdit`). The display names' components are stored with the block. -/
def moveToDisplay (originalAll : Array Name) (rep0 : Name) (perm : Array (Option Nat))
    (sel : Name → Bool) : CompileM Unit := do
  let st ← getBlockState
  let registered : Array Name := st.auxNameToAddr.fold (init := st.auxNamed.map (·.1))
    fun acc n _ => acc.push n
  let mut display : Std.HashMap ExactName Name := {}
  for n in registered do
    if display.contains n || hasReserved n || !sel n then continue
    if let some d := ixAuxName originalAll rep0 perm n then
      display := display.insert n d
  if display.isEmpty then return
  let edit : SideCarEdit := { display }
  let (named, n2a, extra) := edit.apply st.auxNamed st.auxNameToAddr st.auxGenExtraNames
  modifyBlockState fun st => { st with
    auxNamed := named, auxNameToAddr := n2a, auxGenExtraNames := extra }
  for (_, d) in display do compileName d

/-- The heads of a Lean block that get images: its image kinds
(`imageKinds`) that source recognition admits (`casesOn`/`recOn` recognized
as the generated wrappers, the `below`/`brecOn` family recognized whole). -/
def sourceImageHeads (env : Ix.Environment) (all : Array Name) : Array Name :=
  Ix.AuxGen.SourceFamily.filterHeads env all <|
    (imageKinds env.get? all).filter (Ix.AuxGen.SourceIdentity.permitsOptimization env)

/-- Hook 1 of a changed block: the side-car edit (every Ix auxiliary to its
`_ix` display name), and what the block publishes: its heads, its Lean
`all`, its canonical recursors `recs`. -/
def editChangedBlock (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) (recs : Array (Name × RecursorVal)) :
    CompileM Published := do
  let cenv ← getCompileEnv
  let some (originalAll, rep0, perm) := displayInputs cs classNames layout? | return {}
  let some all0 := originalAll[0]? | return {}
  let heads := sourceImageHeads cenv.env originalAll
  -- every Lean name moves off the Ix auxiliaries: the image kinds denote
  -- their images (compiled when their own block comes up, `runImageBlock`),
  -- the rest are Lean's own blocks
  moveToDisplay originalAll rep0 perm fun _ => true
  return { heads := heads.map (·, all0), blocks := #[(all0, originalAll)], canonRecs := recs }

/-! ### Hook 1b: the `IndPredBelow` family of an unchanged block (A3V-IPB)

Lean's `IndPredBelow` family of a Prop block (`all₀.below` an inductive, its
`all` one `below` per motive of the block's recursor) is a Lean block of its
own. Pass 2 builds the Ix family over the canonical block and Pass 1 orders
it, so it can be stored permuted while its parent is unchanged (nested
auxiliaries: Lean's `[A.below, B.below, A.below_1]` against Ix's
`[A.below, A.below_1, B.below]`). Then the family is treated as a changed
block whose members are Lean's `below` inductives: the inductives and
constructors keep Lean's names (each denotes the same inductive, at another
position), the family's Ix auxiliaries (`.rec`, `.casesOn`) move to their
display names (`A.below._ix.rec`), and the family publishes its heads, its
Lean `all` and its canonical recursors, so that Lean's `A.below.rec` and
`A.below.casesOn` compile to their images. Decided from stored positions:
nothing moves unless every member of Lean's family is registered by this tail
at a projection of one stored block, at pairwise distinct positions that
are not Lean's order, and the tail generated the family's recursors. -/

/-- Lean's `IndPredBelow` family of a block: the `all` of `all₀.below` when
that is an inductive of Lean's environment. -/
def leanBelowAll (const? : Name → Option ConstantInfo) (originalAll : Array Name) :
    Array Name :=
  match originalAll[0]? with
  | none => #[]
  | some all0 => match const? (Name.mkStr all0 "below") with
    | some (.inductInfo v) => v.all
    | _ => #[]

/-- The stored positions of `names` in the one inductive block the aux tail
registered them in (`none` when a name is unregistered, not an inductive
projection, or the names span several blocks). -/
def storedPositions (st : BlockState) (names : Array Name) : Option (Array Nat) := do
  let consts : Std.HashMap Address Ixon.Constant :=
    st.auxConsts.foldl (fun m (a, c) => m.insert a c) {}
  let mut block? : Option Address := none
  let mut out : Array Nat := #[]
  for n in names do
    let a ← st.auxNameToAddr.get? n
    let c ← consts.get? a
    let .iPrj p := c.info | none
    if let some b := block? then
      if b != p.block then none
    block? := some p.block
    out := out.push p.idx.toNat
  return out

/-- Hook 1b (A3V-IPB): a permuted `IndPredBelow` family of an unchanged
block, treated as a changed block (see the section docstring). -/
def editPermutedBelowFamily (cs : Array MutConst) (belowRecs : Array (Name × RecursorVal)) :
    CompileM Published := do
  let cenv ← getCompileEnv
  let belowAll := leanBelowAll cenv.env.get? (leanAllOf cs)
  let some all0 := belowAll[0]? | return {}
  if belowAll.size < 2 || belowRecs.isEmpty then return {}
  let some pos := storedPositions (← getBlockState) belowAll | return {}
  if pos == Array.range pos.size then return {}
  -- a permutation only (a collapse inside the family is left as it is)
  if (pos.foldl (init := ({} : Std.HashSet Nat)) (·.insert ·)).size != pos.size then return {}
  -- the family's first member in canonical (stored) order
  let some k := pos.findIdx? (· == 0) | return {}
  let some rep0 := belowAll[k]? | return {}
  let ctors : Std.HashSet Name := belowAll.foldl (init := {}) fun s b =>
    match cenv.env.get? b with
    | some (.inductInfo v) => v.ctors.foldl (·.insert ·) s
    | _ => s
  -- the Ix auxiliaries of the family (not its inductives or constructors)
  moveToDisplay belowAll rep0 #[] fun n =>
    !belowAll.contains n && !ctors.contains n
      && belowAll.any fun b => (stripPrefix? b n).isSome
  let heads := sourceImageHeads cenv.env belowAll
  return { heads := heads.map (·, all0), blocks := #[(all0, belowAll)], canonRecs := belowRecs }

/-- **Hook 1**, after a block's aux tail: `editChangedBlock` for a changed
block, else `editPermutedBelowFamily`. `recs` and `belowRecs` are the
canonical recursors the tail generated (`Ix.AuxGen.AuxTailRecs`). -/
def editBlock (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) (recs belowRecs : Array (Name × RecursorVal)) :
    CompileM Published :=
  if Ix.Compile.ChangedSet.isChanged (leanAllOf cs) classNames layout? then
    editChangedBlock cs classNames layout? recs
  else
    editPermutedBelowFamily cs belowRecs

/-! ## Hook 2: before a block compiles -/

/-- The heads a constant's terms mention, each once, in the order a walk over
distinct subterms meets them. -/
def headsIn (heads : Std.HashMap ExactName Name) (ci : ConstantInfo) : Array Name := Id.run do
  let mut roots : Array Expr := #[ci.getCnst.type]
  match ci with
  | .defnInfo v => roots := roots.push v.value
  | .thmInfo v => roots := roots.push v.value
  | .opaqueInfo v => roots := roots.push v.value
  | .recInfo v => roots := roots ++ v.rules.map (·.rhs)
  | _ => pure ()
  let mut seen : Std.HashSet Ix.Compile.ExactKey.ExprKey := {}
  let mut found : Std.HashSet ExactName := {}
  let mut out : Array Name := #[]
  let mut stack := roots.reverse
  while !stack.isEmpty do
    let some x := stack.back? | break
    stack := stack.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .const n _ _ =>
      if heads.contains n && !found.contains n then
        found := found.insert n
        out := out.push n
    | .app f a _ => stack := stack.push a |>.push f
    | .lam _ t b _ _ | .forallE _ t b _ _ => stack := stack.push b |>.push t
    | .letE _ t v b _ _ => stack := stack.push b |>.push v |>.push t
    | .proj _ _ s _ | .mdata _ s _ => stack := stack.push s
    | _ => pure ()
  return out

/-- The view input of a compile environment: its input constants, its
compiled addresses, its compiled classes (how an external occurrence opens
its group, as the aux tail's canonical expansion opens it) and the published
canonical recursors. -/
def viewInput (cenv : CompileEnv) : ViewInput :=
  { source := cenv.env, addr? := resolveAddr cenv
    groupOf := Ix.Compile.Canon.groupOfBlocks cenv.blocks
    canonRec? := fun n => cenv.p3CanonRecs.get? n }

/-- The Lean `all` of the changed block `key`. -/
def blockAll (cenv : CompileEnv) (key : Name) : Array Name :=
  (cenv.p3Blocks.get? key).getD #[key]

/-- A view of the changed block `key` built now may enter the view memo:
every member of the Lean block is compiled, so the view is a function of
the block and of compiled constants, which no later block changes. -/
def viewMemoable (cenv : CompileEnv) (key : Name) : Bool :=
  (blockAll cenv key).all fun n => (resolveAddr cenv n).isSome

/-- The view of the changed block `key`: from `views` (built by this
block), the view memo, or built (`buildView`). -/
def viewOf (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView) (key : Name) :
    Except String BlockView :=
  match views.get? key with
  | some v => pure v
  | none => memoLookup cenv.p3Views false "Pass 3 view" key fun _ =>
      buildView (viewInput cenv) (blockAll cenv key)

/-- The views this block built that may enter the view memo. -/
def newMemoViews (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView) :
    Array (Name × BlockView) :=
  views.fold (init := #[]) fun acc k v =>
    if !cenv.p3Views.contains k && viewMemoable cenv k then acc.push (k, v) else acc

/-- The views of the changed blocks of `heads`, built once per block. -/
def viewsOf (cenv : CompileEnv) (heads : Array Name) :
    Except String (Std.HashMap ExactName BlockView) := do
  let mut views : Std.HashMap ExactName BlockView := {}
  for h in heads do
    if let some key := cenv.p3Heads.get? h then
      if !views.contains key then
        views := views.insert key (← viewOf cenv views key)
  return views

/-- The expansion of `n` in a rewrite: `none` unless `n` is a head; from the
image memo when there (a recursor's image, or a definitional head's expansion
already rewritten); otherwise from its block's view (the views of `views`,
else built). -/
def expansionLookup (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView) :
    Name → Except String (Option Expansion) := fun n =>
  match cenv.p3Heads.get? n with
  | none => pure none
  | some key =>
    match cenv.p3ImageExps.get? n with
    | some (x, _) => pure (some x)
    | none => do
      let v ← viewOf cenv views key
      let (x, _) ← v.expansion (viewInput cenv) n
      pure (some x)

/-- The first member of the changed blocks `keys` that has not compiled. -/
def unresolvedMember (cenv : CompileEnv) (keys : Array Name) : Option Name := Id.run do
  for key in keys do
    for n in blockAll cenv key do
      if (resolveAddr cenv n).isNone then return some n
  return none

/-- A failure of Pass 3 over the changed blocks `keys` (their views, the
images, a rewrite through them), as the block's error. When a member of one
of those blocks has not compiled, its block failed, and the failure is that
member's cascade: `missingConstant`, as for any dependent of a failed block
(the views need the members' canonical recursors), so the refusal of the
failed block stays the listed cause (`compile-lean`'s bounded listing puts
cascades last). Otherwise the failure itself. -/
def pass3Failure (cenv : CompileEnv) (keys : Array Name) (e : String) : CompileError :=
  match unresolvedMember cenv keys with
  | some n => .missingConstant s!"{n}"
  | none => .invalidMutualBlock e

/-- **Hook 2**, before a block compiles: its members rewritten when they
reference a head, as the block's compile environment (the overlay of the
rewritten members over the input, and the block's decompile sources), with
what the block publishes (the views it built). Identity, and nothing
published, when no head is referenced. -/
def prepareBlock (cenv : CompileEnv) (all : Set Name) (lo : Name) :
    Except CompileError (CompileEnv × Published) := do
  if cenv.p3Heads.isEmpty then return (cenv, {})
  -- the condensation's references first: no head among them, no walk
  if let some refs := cenv.p3BlockRefs.get? lo then
    let referenced := Id.run do
      for n in refs do
        if cenv.p3Heads.contains n then return true
      return false
    if !referenced then return (cenv, {})
  let mut members : Array (Name × ConstantInfo) := #[]
  let mut used : Array Name := #[]
  for n in all do
    if let some ci := cenv.env.get? n then
      members := members.push (n, ci)
      for h in headsIn cenv.p3Heads ci do
        if !used.contains h then used := used.push h
  if used.isEmpty then return (cenv, {})
  let fail := pass3Failure cenv (used.filterMap fun h => cenv.p3Heads.get? h)
  let views ← (viewsOf cenv used).mapError fail
  let published : Published := { views := newMemoViews cenv views }
  let rwr ← (rewriteBlock (expansionLookup cenv views) members).mapError fail
  -- only bare or partial occurrences: nothing rewritten
  if rwr.overlay.isEmpty then return (cenv, published)
  let overlay : Std.HashMap Name ConstantInfo :=
    rwr.overlay.foldl (fun m (n, ci) => m.insert n ci) {}
  let sources : Std.HashMap Nat Expr :=
    rwr.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) {}
  -- the rewritten members over the input, read through `fallback?` (the
  -- input's materialized constants count as unmaterialized in this view, so
  -- `env.consts.size + unmaterialized`, the source-claim walk's bound, is
  -- unchanged)
  let base := cenv.env
  let env : Ix.Environment :=
    { consts := {}, fallback? := some fun n => (overlay.get? n).orElse fun _ => base.get? n }
  return ({ cenv with env, unmaterialized := cenv.unmaterialized + base.consts.size
                      p3Sources := sources }, published)

/-! ## Image blocks: the Lean names of a changed block's auxiliaries -/

/-- Every member of the block is an image-kind head: the block compiles to
the images. -/
def isImageBlock (cenv : CompileEnv) (all : Set Name) : Bool := Id.run do
  if cenv.p3Heads.isEmpty || all.isEmpty then return false
  for n in all do
    if !cenv.p3Heads.contains n then return false
  return true

/-- The image constant of head `a` (expansion `x`, image type `ty`) as an
ordinary definition: its value and type with every head rewritten (no
records), from and to a rewrite state carried over the block's members. -/
def imageDecl (cenv : CompileEnv) (views : Std.HashMap ExactName BlockView) (a : Name)
    (x : Expansion) (ty : Expr) (st0 : RwState) : Except String (Ix.DefinitionVal × RwState) := do
  let lookup := expansionLookup cenv views
  let rwM : RwM (Expr × Expr) := do
    -- the head's own rewritten expansion, when the state holds it
    -- (`expansionOf` computes exactly this value)
    let value ← match (← get).exps.get? a with
      | some e => pure e.value
      | none =>
        if x.needsRewrite then Prod.fst <$> rw lookup rewriteFuel false x.value
        else pure x.value
    let (type, _) ← rw lookup rewriteFuel false ty
    pure (value, type)
  let ((value, type), st) ← (rwM.run {}).run st0
  let safety : Lean.DefinitionSafety := match cenv.env.get? a with
    | some (.defnInfo d) => d.safety
    | some (.recInfo r) => if r.isUnsafe then .unsafe else .safe
    | _ => .safe
  return ({ cnst := { name := a, levelParams := x.levelParams, type }
            value, hints := .abbrev, safety, all := #[a] }, st)

/-- The image constant with Lean's kind: the image of a Lean theorem (a Prop
family's `brecOn`, every `brecOn.eq`) is a theorem, the image of anything
else a definition. -/
def imageInfo (cenv : CompileEnv) (dv : Ix.DefinitionVal) : ConstantInfo :=
  match cenv.env.get? dv.cnst.name with
  | some (.thmInfo _) => .thmInfo { cnst := dv.cnst, value := dv.value, all := dv.all }
  | _ => .defnInfo dv

/-- Compile an image constant; `known` resolves the block's earlier images. -/
def compileImage (cenv : CompileEnv) (known : Std.HashMap ExactName Address)
    (ci : ConstantInfo) : Except String (BlockResult × BlockState) :=
  let name := ci.getCnst.name
  let blockEnv : BlockEnv := { all := ({} : Set Name).insert name, current := name,
                               mutCtx := default, univCtx := [] }
  match CompileM.run cenv blockEnv { blockNameToAddr := known } (compileConstantInfo ci) with
  | .ok r => .ok r
  | .error e => .error s!"Pass 3: image constant {name.pretty}: {e}"

/-- Every head the rewrite state `st` read (`RwState.exps`) is of a changed
block whose view may enter the memo (`viewMemoable`): a value the rewrite
computed from them (its expansions, read with the default `RwConfig`, which
records nothing at no site) is then a function of memoable views and the
input, the same in every later block. -/
def readsMemoable (cenv : CompileEnv) (st : RwState) : Bool :=
  st.exps.fold (init := true) fun ok n _ =>
    ok && match cenv.p3Heads.get? n with
      | some key => viewMemoable cenv key
      | none => false

/-- The images of an image block (`isImageBlock`), compiled in the members'
order by pretty name, each once the images of the block it references are
(rounds), with what the block publishes: the views it built, the recursor
images it computed and the definitional heads' rewritten expansions, when the
views they read may enter the memo (`readsMemoable`). -/
def compileImageBlock (cenv : CompileEnv) (all : Set Name) :
    Except String (Array (Name × BlockResult × BlockState) × Published) := do
  let members := all.toArray.qsort fun a b => a.pretty < b.pretty
  for a in members do
    unless cenv.p3Heads.contains a do throw s!"Pass 3: {a.pretty} is not an image-kind head"
  let views ← viewsOf cenv members
  let inp := viewInput cenv
  -- the image declarations, one rewrite state for the block
  let mut st : RwState := {}
  let mut decls : Array (Name × ConstantInfo) := #[]
  let mut exps : Array (Name × (Expansion × Expr)) := #[]
  for a in members do
    let some key := cenv.p3Heads.get? a | throw s!"Pass 3: {a.pretty} is not an image-kind head"
    let (x, ty) ← match cenv.p3ImageExps.get? a with
      | some xt => pure xt
      | none => do
        let v ← viewOf cenv views key
        let xt ← v.expansion inp a
        if (cenv.env.get? a matches some (.recInfo _)) && viewMemoable cenv key then
          exps := exps.push (a, xt)
        pure xt
    let st0 := st
    st := {}  -- released, so the run updates the caches in place
    let (dv, st') ← imageDecl cenv views a x ty st0
    st := st'
    -- a definitional head's rewritten expansion enters the image memo: a later
    -- block's rewrite reads it instead of rewriting Lean's value again
    if x.needsRewrite && viewMemoable cenv key && readsMemoable cenv st then
      exps := exps.push (a, ({ x with value := dv.value, needsRewrite := false }, ty))
    decls := decls.push (a, imageInfo cenv dv)
  -- compile, each once the images it references are
  let mut pending := decls
  let mut known : Std.HashMap ExactName Address := {}
  let mut out : Array (Name × BlockResult × BlockState) := #[]
  let mut lastErr := ""
  let mut rounds := pending.size + 1
  while !pending.isEmpty && rounds > 0 do
    rounds := rounds - 1
    let mut rest : Array (Name × ConstantInfo) := #[]
    for (a, ci) in pending do
      match compileImage cenv known ci with
      | .ok (r, bs) =>
        known := known.insert a r.blockAddr
        out := out.push (a, r, bs)
      | .error e =>
        lastErr := e
        rest := rest.push (a, ci)
    pending := rest
  if !pending.isEmpty then throw lastErr
  return (out, { views := newMemoViews cenv views, imageExps := exps })

/-- Compile an image block: its images under the Lean names, each with
`Named.original` = Lean's own form compiled without the aux tail
(`original`, the driver's `compileConstNoAuxPure`), the provenance the
decompiler verifies against. The block's result is `lo`'s image. -/
def runImageBlock
    (original : CompileEnv → Name → Set Name → Except CompileError (BlockResult × BlockState))
    (cenv : CompileEnv) (all : Set Name) (lo : Name) :
    Except CompileError (BlockResult × BlockState × Published) := do
  let (imgs, published) ← (compileImageBlock cenv all).mapError
    (pass3Failure cenv (all.toArray.filterMap fun h => cenv.p3Heads.get? h))
  let (origRes, origCache) ← original cenv lo all
  let origs : Std.HashMap ExactName (Address × Ixon.ConstantMeta) :=
    if origRes.projections.isEmpty then
      ({} : Std.HashMap ExactName _).insert lo (origRes.blockAddr, origRes.blockMeta)
    else origRes.projections.foldl (init := {}) fun m (n, proj, cm) =>
      m.insert n (Address.admissionHash (Ixon.ser proj), cm)
  let mut cache : BlockState :=
    { blockBlobs := origCache.blockBlobs, blockNames := origCache.blockNames }
  let mut result? : Option BlockResult := none
  for (a, r, bs) in imgs do
    cache := { cache with
      auxConsts := cache.auxConsts.push (r.blockAddr, r.block)
      auxNamed := cache.auxNamed.push
        (a, { addr := r.blockAddr, constMeta := r.blockMeta, original := origs.get? a })
      auxNameToAddr := cache.auxNameToAddr.insert a r.blockAddr
      blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) cache.blockBlobs
      blockNames := bs.blockNames.fold (fun m k v => m.insert k v) cache.blockNames
      defHints := bs.defHints.fold (fun m k v => m.insert k v) cache.defHints }
    if nameEq a lo then result? := some r
  let some result := result? | throw (.invalidMutualBlock s!"Pass 3: no image for {lo.pretty}")
  return (result, cache, published)

/-! ## Decompile records: the extension references -/

/-- Each compiled constant's extension references (`BlockState.p3MetaRefs`,
filled by `Ix.CompileM.internRefMeta`) in its metadata
(`ConstantMeta.metaRefs`): the member projections', or the lone constant's
(`lo`). Identity for a block without records. -/
def withMetaRefs (refs : Std.HashMap ExactName MetaRefTable) (lo : Name)
    (r : BlockResult) : BlockResult :=
  if refs.isEmpty then r else
  let patch (n : Name) (m : Ixon.ConstantMeta) : Ixon.ConstantMeta :=
    match refs.get? n with
    | some t => if t.refs.isEmpty then m else { m with metaRefs := t.refs }
    | none => m
  if r.projections.isEmpty then { r with blockMeta := patch lo r.blockMeta }
  else { r with projections := r.projections.map fun (n, c, m) => (n, c, patch n m) }

end Ix.Compile.Pass

end
