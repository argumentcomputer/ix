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

/-- The display-name inputs of a block (`ixAuxName`): Lean's `all`, the first
class representative, the nested source permutation. -/
def displayInputs (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : Option (Array Name × Name × Array (Option Nat)) := do
  let originalAll := leanAllOf cs
  let lookup : Std.HashSet Name := originalAll.foldl (init := {}) (·.insert ·)
  let planClasses := classNames.filterMap fun cls =>
    let ns := cls.filter lookup.contains
    if ns.isEmpty then none else some ns
  let rep0 ← (planClasses[0]?).bind (·[0]?)
  let perm : Array (Option Nat) := match layout? with
    | some l => l.perm.map fun p => if p == permOut then none else some p.toNat
    | none => #[]
  return (originalAll, rep0, perm)

/-- Move the tail's registrations selected by `sel` to their display names
(`SideCarEdit` with nothing kept), returning the display map. -/
def moveToDisplay (originalAll : Array Name) (rep0 : Name) (perm : Array (Option Nat))
    (sel : Name → Bool) : CompileM (Std.HashMap Name Name) := do
  let st ← getBlockState
  let mut display : Std.HashMap Name Name := {}
  for n in st.auxNamed.map (·.1) ++ st.auxNameToAddr.toArray.map (·.1) do
    if display.contains n || !sel n then continue
    if let some d := ixAuxName originalAll rep0 perm n then
      display := display.insert n d
  let edit : SideCarEdit := { display, kept := {} }
  let (named, n2a, extra) := edit.apply st.auxNamed st.auxNameToAddr st.auxGenExtraNames
  for (_, d) in display do compileName d
  modifyBlockState fun st => { st with
    auxNamed := named, auxNameToAddr := n2a, auxGenExtraNames := extra }
  return display

/-- The side-car edit and the driver records of a changed block, applied to
the block state. -/
def editChangedBlock (cs : Array MutConst) (classNames : Array (Array Name))
    (layout? : Option Ixon.AuxLayout) : CompileM Unit := do
  let cenv ← getCompileEnv
  let some (originalAll, rep0, perm) := displayInputs cs classNames layout? | return
  let some all0 := originalAll[0]? | return
  let heads := imageKinds cenv.env.get? originalAll
  -- every Lean name moves off the Ix auxiliaries: the image kinds denote
  -- their stored images (compiled when their own block comes up,
  -- `compileImageBlock`), the rest are Lean's own blocks
  let _ ← moveToDisplay originalAll rep0 perm fun _ => true
  modifyBlockState fun st => { st with
    p3Heads := st.p3Heads ++ heads.map (·, all0)
    p3Blocks := st.p3Blocks.push (all0, originalAll) }

/-! ## Hook 1b: the `IndPredBelow` family of an unchanged block (A3V-IPB)

## Contract
Input: an *unchanged* Lean block (Def 3.1 does not hold) after its aux tail,
under the switch. Lean's `IndPredBelow` family of the block (Prop blocks:
`all₀.below` is an inductive, with Lean's `all` = one `below` per motive of
the block's recursor: `x.below` per member, then `all₀.below_j` per nested
auxiliary) is itself a Lean-generated **inductive block**. Pass 2 builds the
Ix family over the canonical block (`buildPropBelowFamily`) and Pass 1 then
orders it as a block of its own (`sortConsts` in the aux tail's phase 3), so
the family can be *permuted* (or collapsed) while its parent is unchanged
(the nested shapes of `Tests/Ix/Compile/ValidateLeanIPB.lean`: Lean's
`[A.below, B.below, A.below_1]` against Ix's `[A.below, A.below_1, B.below]`).

Output, when the stored member positions of Lean's family names are not
Lean's order (a permutation of it): the family is **treated as a changed
block** whose members are Lean's `below` inductives. As for any permuted
block, the inductives and constructors keep Lean's names (each denotes the
same inductive, now a projection at another position); the Ix auxiliaries
of the family (Pass 2's `.rec`, `.casesOn`) move to their `_ix` display
names (`A.below._ix.rec`: `ixAuxName` over Lean's family `all`); the family
records its image-kind heads, its Lean `all` and Pass 2's canonical
recursors (`p3BelowRecs`), so that Lean's `A.below.rec`, `A.below.casesOn`
compile to their images (Def 3.4, 3.5) when their own blocks come up
(`compileImageBlock`), exactly as for a changed user block. Otherwise
nothing changes.

## Faithfulness
Before this hook Lean's `A.below.rec` named the Ix recursor of the permuted
family: a constant whose motives come in another order than Lean's, i.e. of
a different type (A3V-IPB, found by the validator's oracle leg). After it,
every Lean name of the family denotes a constant with Lean's type: the
inductives and constructors are the canonical family's members, which are
Lean's inductives up to block position (the oracle leg found them equal);
`.rec`/`.casesOn` denote their images, which compute as Lean's recursors
(Def 3.4, re-checked by phase 7 of `ix validate-lean`). Every other entry
changes in metadata only (references to the moved names are renamed to the
display names, which name the same constants).

## Canonicity
Two choices were open (design document §2.5): keep Lean's order for
Lean-generated families, or treat the family as a changed block. The first
is excluded by the kernels: every all-inductive block is checked against the
comparator order (`validateCanonicalBlockSinglePass`, Rust and `Ix.Tc`), so a
family stored in Lean's order would be rejected as non-canonical wherever
Pass 1 orders it differently, which is exactly the A3V-IPB case. The second
keeps the Ix family canonical and byte-identical to the switch-off output (it
is a function of the canonical parent, then of Pass 1) and moves only Lean's
names (Q2: names are metadata): the governing principle's choice. The
decision reads stored positions, a function of the canonical form.

## Side condition and fallback
Decidable: the switch is on, the parent is unchanged, `all₀.below` is an
inductive of Lean's environment with at least two members, every member of
Lean's family is registered by the tail at a projection of one stored block,
at pairwise distinct positions, and the tail recorded the family's canonical
recursors. Otherwise nothing moves: today's registration (a collapsed family,
never observed, would stay as it is; the switch-off path keeps the defect,
recorded by its id A3V-IPB until the switch flips).

## Non-canonical cases and evidence
None new: Lean's `below` recursors and `casesOn` are image kinds of a changed
block like any other (bare occurrences: `BARE`). Evidence: `validate-lean` on
`ValidateLeanIPB` and `Neighbours` (phases 6 and 8 pass with the switch on;
phase 7 checks the images and their rules), the `pass3` suite.
-/

/-- Lean's `IndPredBelow` family of a block: the `all` of `all₀.below` when
that is an inductive of Lean's environment, in Lean's order. -/
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

/-- A3V-IPB: under the switch, treat a permuted `IndPredBelow` family of an
unchanged block as a changed block (see the section docstring). -/
def editPermutedBelowFamily (cs : Array MutConst) : CompileM Unit := do
  let cenv ← getCompileEnv
  let belowAll := leanBelowAll cenv.env.get? (leanAllOf cs)
  let some all0 := belowAll[0]? | return
  if belowAll.size < 2 then return
  let st ← getBlockState
  let some pos := storedPositions st belowAll | return
  if pos == Array.range pos.size then return
  -- a permutation only (a collapse inside the family is left as it is)
  if (pos.foldl (init := ({} : Std.HashSet Nat)) (·.insert ·)).size != pos.size then return
  if st.p3BelowRecs.isEmpty then return
  -- the family's first member in canonical (stored) order
  let some k := pos.findIdx? (· == 0) | return
  let some rep0 := belowAll[k]? | return
  let ctors : Std.HashSet Name := belowAll.foldl (init := {}) fun s b =>
    match cenv.env.get? b with
    | some (.inductInfo v) => v.ctors.foldl (·.insert ·) s
    | _ => s
  -- the Ix auxiliaries of the family (not its inductives or constructors)
  let _ ← moveToDisplay belowAll rep0 #[] fun n =>
    !belowAll.contains n && !ctors.contains n
      && belowAll.any fun b => (stripPrefix? b n).isSome
  let heads := imageKinds cenv.env.get? belowAll
  modifyBlockState fun st => { st with
    p3AuxRecs := st.p3AuxRecs ++ st.p3BelowRecs
    p3Heads := st.p3Heads ++ heads.map (·, all0)
    p3Blocks := st.p3Blocks.push (all0, belowAll) }

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

/-- A view of the changed block `key` built now may enter the view table
(`CompileEnv.p3Views`): every member of the block is compiled. The view reads
the input constants, the canonical recursors of the block (registered when it
compiled) and the addresses of compiled constants (insert-once); with every
member compiled it computes the canonical form of every component, so a block
whose snapshot contains this one's merges builds the same view. -/
def viewMemoable (cenv : CompileEnv) (key : Name) : Bool :=
  ((cenv.p3Blocks.get? key).getD #[key]).all fun n => (resolveAddr cenv n).isSome

/-- The view of the changed Lean block `key`: from the block's own views,
then the view table, else built. -/
def viewOf (cenv : CompileEnv) (views : Std.HashMap Name BlockView) (key : Name) :
    Except String BlockView :=
  match views.get? key with
  | some v => pure v
  | none =>
    match cenv.p3Views.get? key with
    | some v => pure v
    | none => buildView (viewInput cenv) ((cenv.p3Blocks.get? key).getD #[key])

/-- The views among `views` a block built itself that may enter the view table. -/
def newMemoViews (cenv : CompileEnv) (views : Std.HashMap Name BlockView) :
    Array (Name × BlockView) :=
  views.fold (init := #[]) fun acc k v =>
    if !cenv.p3Views.contains k && viewMemoable cenv k then acc.push (k, v) else acc

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

/-- The definitional passes' blocks (`Opt.optBlockOf`) of the given views.
Computed once per rewrite by the caller and passed to `optLookup` and
`declineLookup`: a table computed inside those definitions would be computed
again at every call, since the compiler takes all their arguments at once. -/
def optBlocks (cenv : CompileEnv) (views : Std.HashMap Name BlockView) :
    Std.HashMap Name Opt.OptBlock :=
  let inp := viewInput cenv
  views.fold (fun m k v => m.insert k (Opt.optBlockOf inp v)) {}

/-- `expansionLookup` with one lazily evaluated, cached entry per head
(`Thunk`): a head's expansion (for a recursor, its whole image) is computed
at its first occurrence in the rewrite and reused at every later one. The
same values as `expansionLookup`; built by the caller, once per rewrite. -/
def expansionTable (cenv : CompileEnv) (views : Std.HashMap Name BlockView) :
    Std.HashMap Name (Thunk (Except String (Option Expansion))) :=
  cenv.p3Heads.fold (init := {}) fun m n _ =>
    -- a recursor's expansion is its image, the same in every rewrite
    -- context: taken from the image-expansion memo when there
    match cenv.p3ImageExps.get? n, cenv.env.get? n with
    | some x, some (.recInfo _) => m.insert n (Thunk.pure (.ok (some x)))
    | _, _ => m.insert n (Thunk.mk fun _ => expansionLookup cenv views n)

/-- The lookup of an `expansionTable` (a head outside it: `expansionLookup`). -/
def expansionLookupIn (table : Std.HashMap Name (Thunk (Except String (Option Expansion))))
    (cenv : CompileEnv) (views : Std.HashMap Name BlockView) :
    Name → Except String (Option Expansion) := fun n =>
  match table.get? n with
  | some t => t.get
  | none => expansionLookup cenv views n

/-- `imageDecl` from a given rewrite state (its caches: rewritten
expansions, level-substituted values, rewritten subterms, all without
records), returning the final state. With a state carried over from an
earlier run, `needed` lists only what this run met first. -/
def imageDeclWith (cenv : CompileEnv) (views : Std.HashMap Name BlockView) (a : Name)
    (table : Std.HashMap Name (Thunk (Except String (Option Expansion))))
    (st0 : RwState) : Except String (Ix.DefinitionVal × RwState) := do
  let some key := cenv.p3Heads.get? a | throw s!"Pass 3: {a.pretty} is not an image-kind head"
  let inp := viewInput cenv
  let v ← viewOf cenv views key
  let (x, ty) ← v.expansion inp a
  let lookup := expansionLookupIn table cenv views
  -- the value (and the type) with every head rewritten, no records
  let rwM : RwM (Expr × Expr) := do
    -- the head's own rewritten expansion, when the state already holds it
    -- (`expansionOf` computes exactly this value)
    let x' ← match st0.exps.get? a with
      | some e => pure e.value
      | none => if x.needsRewrite then rw lookup rewriteFuel false x.value else pure x.value
    let ty' ← rw lookup rewriteFuel false ty
    pure (x', ty')
  let ((value, type), st) ← rwM.run st0
  let safety : Lean.DefinitionSafety := match inp.const? a with
    | some (.defnInfo d) => d.safety
    | some (.recInfo r) => if r.isUnsafe then .unsafe else .safe
    | _ => .safe
  let name := a
  return ({ cnst := { name, levelParams := x.levelParams, type }
            value, hints := .abbrev, safety, all := #[name] }, st)

/-- The image constant `a._ix` of a needed head (a bare or partial
occurrence) as an ordinary definition, with the heads its rewritten value
needs in turn (a fresh rewrite state). -/
def imageDecl (cenv : CompileEnv) (views : Std.HashMap Name BlockView) (a : Name) :
    Except String (Ix.DefinitionVal × Array Name) := do
  let (dv, st) ← imageDeclWith cenv views a (expansionTable cenv views) { base := 0 }
  return (dv, st.needed.filter (· != a))

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

/-- The canonical `_ix` form of a compiled dependency (decision 5, D1): `d ↦
d._ix` when `d` is a definition of the input (never an image-kind head) and
`d._ix` is compiled. `d` is referenced by the constant being compiled, so it
is a dependency and its block, which emits `d._ix` with it, compiled first:
the answer is a function of the dependency's compiled form, never of a
caller or of the schedule. Read only by O10 and O12, which compare handlers
through their references' canonical forms (`OptEnv.canonAddrOf`); no
reference is renamed to it (`compileCanon`). -/
def ixFormOf (cenv : CompileEnv) (d : Name) : Option Name :=
  match cenv.env.get? d with
  | some (.defnInfo _) =>
    if cenv.p3Heads.contains d then none
    else
      let c := ixFormName d
      if (resolveAddr cenv c).isSome then some c else none
  | _ => none

/-- The optimisation passes (`Ix.Compile.Pass.Opt.engineFull`) over the
definitional passes' blocks of a block's referenced changed blocks
(`optBlocks`, computed once by the caller): the hook the rewrite tries at
every full application before it inlines an image (heads of other blocks
keep their baseline). The result says whether the pass is proof-justified
(`Opt.isProofJustified`), whose output goes to the canonical `_ix` form only
(D1, `Translate.RwState.inPlace`). -/
def optLookup (cenv : CompileEnv) (blocks : Std.HashMap Name Opt.OptBlock) :
    Option Name → Name → Array Ix.Level → Array Expr → Option (Expr × Array ConstantInfo × Bool) :=
  let env : Opt.OptEnv :=
    { ienv := cenv.env, resolves := fun n => (resolveAddr cenv n).isSome
      blockOf := fun h => (cenv.p3Heads.get? h).bind blocks.get?
      addrOf := resolveAddr cenv
      ixForm? := ixFormOf cenv }
  fun site n us args => (Opt.engineFull env { head := n, us, args, site }).map fun (nm, e, cs) =>
    (e, cs, Opt.isProofJustified nm)

/-- The unit passes (A6p) over a block's members: O11b gives Lean's
`noConfusion` pair of a split-off enumeration its enumeration form
(`Ix.Compile.Pass.Opt.O11b`). Decision 5 (D1): the Lean names keep Lean's
general form; the enumeration form is returned as the canonical constants
`T.noConfusionType._ix`, `T.noConfusion._ix` (compiled with the block by
`compileCanon`); the type of `T.noConfusion._ix` refers to
`T.noConfusionType._ix` (the pair is one decision, Lemma O11b.2). -/
def unitPasses (cenv : CompileEnv) (views : Std.HashMap Name BlockView)
    (members : Array (Name × ConstantInfo)) : Array ConstantInfo := Id.run do
  let classesOf : Name → Option (Array (Array Name)) := fun t => do
    let key ← cenv.p3Heads.get? (Name.mkStr t "casesOn")
    let v ← views.get? key
    let c ← v.canon.components.find? (·.members.contains t)
    pure c.classes
  let mut canon : Array ConstantInfo := #[]
  for (n, ci) in members do
    let some dv := Opt.O11b.rewrite cenv.env.get? classesOf n ci | continue
    let c := ixFormName n
    -- the pair is decided together (`O11b.pairApplies`): the canonical
    -- `noConfusion` is typed over the canonical `noConfusionType` (Lemma O11b.2)
    let ty := match Opt.noConfusionOf n with
      | some (t, false) =>
        let nct := Name.mkStr t "noConfusionType"
        Ix.Compile.Canon.canonicalizeConstNames (({} : Std.HashMap Name Name).insert nct (ixFormName nct)) dv.cnst.type
      | _ => dv.cnst.type
    canon := canon.push (.defnInfo { dv with cnst := { dv.cnst with name := c, type := ty }, all := #[c] })
  return canon

/-- The recorded declines of the definitional passes over the same views
(`Ix.Compile.Pass.Opt.O11a.declineCause?`): the hook the rewrite tries next
to `optLookup`, giving the cause when O11a declined because an instance its
output needs is absent from the input. -/
def declineLookup (cenv : CompileEnv) (blocks : Std.HashMap Name Opt.OptBlock) :
    Name → Array Ix.Level → Array Expr → Option String :=
  let env : Opt.OptEnv :=
    { ienv := cenv.env, resolves := fun n => (resolveAddr cenv n).isSome
      blockOf := fun h => (cenv.p3Heads.get? h).bind blocks.get? }
  fun n us args => Opt.O11a.declineCause? env { head := n, us, args }

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
  let table := expansionTable cenv views
  rewriteBlock (expansionLookupIn table cenv views) members (optLookup cenv (optBlocks cenv views))

/-- Compile the block's canonical constants (reserved `_ix` names) into its
initial state, the way A5's clique hook compiles its canonical constants:
* the canonical forms `c._ix` of the block's definitions where a
  proof-justified pass fires (decision 5, D1; `Translate.RwState.canon`) and
  O11b's (`unitPasses`), and the helpers the passes' rewrites reference
  (O9/O10's re-typed handlers `p._ix_retyped.s`, O12's `fg`);
* each through the call-site rewrite **in place** (`rewriteBlock` with
  `inPlace`: the proof-justified passes rewrite a canonical constant itself),
  whose own helpers join the work list;
* no reference is renamed afterwards: a canonical constant refers to its
  dependencies by their Lean names, so it is well typed whatever forms they
  have (a raw renaming `d ↦ d._ix` is not conversion-preserving); a caller
  that wants a canonical form refers to it itself (callers adapt, §6.3);
* then compiled as ordinary constants, each once the canonical constants it
  references are. A reserved name already bound (O12's `fg`, emitted by the
  blocks of both functions of a pair; a canonical constant of the clique hook)
  must be bound to the same bytes, which are then not stored again (the
  driver's insert-once merge); a different binding fails the compile (a
  reserved-name clash is refused, never resolved silently). -/
def compileCanon (cenv : CompileEnv) (views : Std.HashMap Name BlockView)
    (canon : Array ConstantInfo) (init0 : BlockState := {}) : Except String BlockState := do
  let lookup := expansionLookupIn (expansionTable cenv views) cenv views
  let opt := optLookup cenv (optBlocks cenv views)
  -- rewrite in place, collecting the helpers the rewrites reference
  let mut queue := canon
  let mut i := 0
  let mut seen : Std.HashSet Name := {}
  let mut done : Array (ConstantInfo × Std.HashMap Nat Expr) := #[]
  while h : i < queue.size do
    let ci := queue[i]
    i := i + 1
    let c := ci.getCnst.name
    if seen.contains c then continue
    seen := seen.insert c
    let rw ← rewriteBlock lookup #[(c, ci)] opt (inPlace := true)
    let ci' := match rw.overlay[0]? with
      | some (_, x) => x
      | none => ci
    queue := queue ++ rw.canon
    let srcs : Std.HashMap Nat Expr := rw.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) {}
    done := done.push (ci', srcs)
  -- no reference is renamed here: a canonical constant refers to its
  -- dependencies by their Lean names (a raw renaming d ↦ d._ix is not
  -- conversion-preserving: a constant whose type mentions d would then be
  -- applied to a term built with d._ix; measured, the certified checker
  -- rejects such `noConfusionType._ix`). A caller that wants a canonical form
  -- refers to it itself (O9/O12: their helpers; O11b: its pair).
  let compiled := done
  -- compile, each once its canonical references are compiled
  let names : Std.HashSet Name := compiled.foldl (fun s (ci, _) => s.insert ci.getCnst.name) {}
  let mut init : BlockState := init0
  let mut pending := compiled
  let mut rounds := pending.size + 1
  while !pending.isEmpty && rounds > 0 do
    rounds := rounds - 1
    let mut rest := #[]
    for (ci, srcs) in pending do
      let c := ci.getCnst.name
      let refs := constsWhere (fun r => names.contains r && r != c) ci.getCnst.type ++
        (match ci with | .defnInfo d => constsWhere (fun r => names.contains r && r != c) d.value | _ => #[])
      if refs.any (!init.blockNameToAddr.contains ·) then
        rest := rest.push (ci, srcs)
        continue
      let blockEnv : BlockEnv :=
        { all := ({} : Ix.Set Name).insert c, current := c, mutCtx := default, univCtx := [] }
      let st0 : BlockState := { blockNameToAddr := init.blockNameToAddr }
      match CompileM.run { cenv with p3Sources := srcs } blockEnv st0 (compileConstantInfo ci) with
      | .error e => throw s!"Pass 3 optimisations: canonical constant {c.pretty}: {e}"
      | .ok (r, bs) =>
        -- a reserved name already bound (O12's `fg`, emitted by both functions'
        -- blocks; the clique hook's canonical constants): the same bytes, or a
        -- clash, which fails closed rather than binding another constant
        match (resolveAddr cenv c).orElse fun _ => init.blockNameToAddr.get? c with
        | some a =>
          if a != r.blockAddr then
            throw s!"Pass 3 optimisations: reserved name {c.pretty} is already bound to {a}, not to the canonical constant {r.blockAddr}"
          init := { init with blockNameToAddr := init.blockNameToAddr.insert c a }
        | none =>
          init := { init with
            blockNameToAddr := init.blockNameToAddr.insert c r.blockAddr
            auxConsts := init.auxConsts.push (r.blockAddr, r.block)
            auxNamed := init.auxNamed.push (c, { addr := r.blockAddr, constMeta := r.blockMeta })
            auxNameToAddr := init.auxNameToAddr.insert c r.blockAddr
            blockBlobs := bs.blockBlobs.fold (fun m k v => m.insert k v) init.blockBlobs
            blockNames := bs.blockNames.fold (fun m k v => m.insert k v) init.blockNames
            defHints := bs.defHints.fold (fun m k v => m.insert k v) init.defHints }
    pending := rest
  if !pending.isEmpty then
    throw s!"Pass 3 optimisations: canonical constants with cyclic references: {pending.map (·.1.getCnst.name.pretty)}"
  return init

/-- Rewrite a block before it compiles: the compile environment (overlay,
decompile sources) and the initial block state (stored image constants).
Identity when the switch is off or the block references no head. -/
def prepareBlock (cenv : CompileEnv) (all : Set Name) (lo : Name) :
    Except String (CompileEnv × BlockState) := do
  if !cenv.pass3 then return (cenv, {})
  -- changed definition cliques (`Ix.Compile.Pass.Cliques`, the A5 hook): the
  -- members' transported values with their decompile records, and the
  -- canonical constants they reference
  let (cenv, init) ← Ix.PhaseTimers.withPhase .p3Cliques cenv fun cenv =>
    prepareCliques cenv all (cenv.p3BlockRefs.getD lo {}) (cliqueRewrite cenv)
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
  let table := expansionTable cenv views
  let blocks := optBlocks cenv views
  let rwr ← rewriteBlock (expansionLookupIn table cenv views) members (optLookup cenv blocks)
    (declineLookup cenv blocks)
  let overlay : Std.HashMap Name ConstantInfo :=
    rwr.overlay.foldl (fun m (n, ci) => m.insert n ci) cenv.env.overlay
  let sources : Std.HashMap Nat Expr :=
    rwr.sources.zipIdx.foldl (fun m (e, i) => m.insert i e) cenv.p3Sources
  -- the recorded declines go to the block state, and from there into the
  -- compile's non-canonical set (`CompileEnv.p3NonCanonical`)
  let init := { init with p3NonCanonical := init.p3NonCanonical ++ rwr.declines,
                           p3MemoViews := init.p3MemoViews ++ newMemoViews cenv views }
  -- the canonical constants (D1): the `_ix` forms where a proof-justified
  -- pass fires, the unit passes' (O11b), the helpers the rewrites reference
  let init ← compileCanon cenv views (rwr.canon ++ unitPasses cenv views members) init
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
    Except String (Array (Name × BlockResult × BlockState)
      × Array (Name × BlockView) × Array (Name × Expansion)) := do
  let mut views : Std.HashMap Name BlockView := {}
  for a in all do
    if let some key := cenv.p3Heads.get? a then
      if !views.contains key then views := views.insert key (← viewOf cenv views key)
  let mut pending := all.toArray.qsort (fun a b => a.pretty < b.pretty)
  let mut known : Std.HashMap Name Address := {}
  let mut out : Array (Name × BlockResult × BlockState) := #[]
  let mut lastErr := ""
  let mut decls : Std.HashMap Name Ix.DefinitionVal := {}
  let table := expansionTable cenv views
  -- one rewrite state for the block's members: its caches carry over, and it
  -- starts from the image-expansion memo (`CompileEnv.p3ImageExps`)
  let mut rwSt : RwState := { base := 0, exps := cenv.p3ImageExps }
  let mut rounds := pending.size + 1
  while !pending.isEmpty && rounds > 0 do
    rounds := rounds - 1
    let mut rest : Array Name := #[]
    for a in pending do
      -- `imageDecl` does not read `known`: a member retried in a later round
      -- reuses its declaration
      if !decls.contains a then
        let st0 := { rwSt with sources := #[], needed := #[], declines := #[] }
        rwSt := { base := 0 }  -- released, so the run updates the caches in place
        let (dv, st) ← imageDeclWith cenv views a table st0
        rwSt := st
        decls := decls.insert a dv
      let some dv := decls.get? a | throw s!"Pass 3: no image declaration for {a.pretty}"
      match compileImage cenv known dv with
      | .ok (r, bs) =>
        known := known.insert a r.blockAddr
        out := out.push (a, r, bs)
      | .error e =>
        lastErr := e
        rest := rest.push a
    pending := rest
  if !pending.isEmpty then throw lastErr
  -- memo entries: the views built here, and the expansions computed here when
  -- every changed block they read has a memoable view
  let memoViews := newMemoViews cenv views
  let newExps := rwSt.exps.fold (init := #[]) fun acc n x =>
    if cenv.p3ImageExps.contains n then acc else acc.push (n, x)
  let expsOk := views.keys.all (viewMemoable cenv) &&
    newExps.all fun (n, _) => match cenv.p3Heads.get? n with
      | some key => viewMemoable cenv key
      | none => false
  return (out, memoViews, if expsOk then newExps else #[])



end Ix.Compile.Pass

end
