/-
  Ix.Compile.Canon.Nested: nested auxiliaries of a block, their order, and
  evaporation, as total functions.

  ## The expansion

  A block with nested occurrences (`List T`, `Array (Part α)`) is flattened
  into a mutual block whose auxiliary members stand for the occurrences.
  `expand` is Lean's kernel construction `elim_nested_inductive_fn`
  (`src/kernel/inductive.cpp:985-1180`, Lean 4.34.1), which the compiler
  mirrors in `Ix.AuxGen.expandNestedBlock` (Rust `expand_nested_block`):

  * a FIFO queue of types, initially the members in the given order; the
    head of the queue has each of its constructors processed in order;
  * a constructor type has its first `numParams` binders peeled; the rest is
    walked by Lean's `replace`, in pre-order: a node is first tested as a
    nested occurrence, and only if it is not one are its children visited
    (application: function, then argument; binder: domain, then body;
    `let`: type, value, body; projection and `mdata`: the inner term);
  * a node `I Ds is` is a nested occurrence when `I` is an inductive outside
    the queue's names, has at least `numParams I` arguments, some parameter
    argument `D` mentions a name in the queue, and no `D` mentions a
    variable bound inside the constructor (Lean rejects that declaration;
    the compiler skips the node and walks into it);
  * a new occurrence appends one auxiliary per member `J` of `I`'s mutual
    group, in `I.all` order (type and constructors instantiated at the
    occurrence's levels and parameters), to the end of the queue, and the
    node is replaced by the auxiliary of `I` applied to the block parameters
    and the indices `is`;
  * an occurrence already seen is replaced by its auxiliary.

  **Discovery order** is the order in which the auxiliaries are appended.
  Lean numbers the recursors of the source block's auxiliaries
  `all₀.rec_1, …, all₀.rec_k` in exactly this order (`mk_aux_rec_name_map`),
  which `recMajorSignatures` reads back for validation.

  **Deduplication models** (`Dedup`): `Dedup.compiler` retains the
  historical trigger-only policy: record only `I Ds`, pointing to the
  group's first auxiliary. A non-first member or two siblings can then
  select the wrong auxiliary or create a second group. `Dedup.lean`
  records every member of each new group/class. The current production
  `Ix/AuxGen/Nested.lean` `replaceIfNested` and Rust `replace_if_nested`
  also iterate every class member and insert its occurrence key when absent; the
  historical constructor name is not a description of today's compiler.
  This correspondence of the registration clauses is not a proof that
  the full runtime expansion equals this total model; that remains part
  of the general obligations in `docs/compiler-certification.md` §1.7.

  ## Orders

  * `NestedOrder.structural` (`Rules.today`, the compiler before
    A2-order): the auxiliaries, each with a trailing identity-marker
    constructor typed by its occurrence (block parameters as `bvar i`,
    literally, as the compiler did), are sorted by `Classes.sortClasses`
    with today's rules; references to the block's members are external (by
    address). Kept for the census's `today` column (`structuralAuxClasses`).
  * `NestedOrder.discovery` (Phase A; what the compiler runs, A2-order):
    the discovery order of the expansion of the canonical block (members in
    canonical order, collapsed members renamed to their representatives,
    Lean's deduplication of sibling occurrences). An external group opens
    as `SourceGroups` says: Lean's `I.all` (`leanSourceGroup`), or, in the compiler, the
    external block's compiled canonical classes (`sourceGroupsOfBlocks`), which is
    what the kernels recompute from the stored Ixon; the two agree whenever
    the external block is an identity block. The compiler reads this order
    through `canonicalAuxOrder` (`sortAuxByPartitionRefinement`), and it is
    the identity on the canonical expansion.

  `perm` maps each of Lean's source positions (discovery order over the
  block's `all`) to its canonical position (`computeAuxPerm`): signatures
  `(head, levels, parameters)` are matched first with equal levels, then
  with any levels, parameters equal up to `auxSpecEq` (constants by name or
  address, members outside the component strictly by name). `none` is
  today's `PERM_OUT_OF_SCC`.

  ## Evaporation

  `evaporated` is today's `AuxLayout.evaporated`
  (`Ix/AuxGen/Patches.lean:620-716`): a source position whose owner is in
  the component, that has no canonical position there (`perm = none`), that
  Lean exported (`all₀.rec_{j+1}` exists), that no other component of the
  block discovers canonically, and whose external head's recursor has one
  motive. The cross-component probe needs the other components' canonical
  signatures and is done by `Block.lean`.

  Everything here is in de Bruijn form: inside a constructor, below its
  `numParams` peeled binders, a block parameter `i` under `d` further
  binders is `bvar (d + numParams - 1 - i)`. Occurrence parameters are
  stored at depth 0 (`bvar (numParams - 1 - i)` for parameter `i`).
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Canon.OccurrenceKey
public import Ix.Compile.Canon.SourceFast
public import Ix.Compile.Canon.FreshNames
public import Ix.Compile.Canon.Order
public import Ix.Compile.Canon.Classes
public section

namespace Ix.Compile.Canon

open Ix (Name Level Expr ConstantInfo MutConst ConstructorVal)

/-! ## Inductive views -/

/-- What the expansion reads of an inductive. -/
structure IndView where
  name : Name
  levelParams : Array Name
  type : Expr
  numParams : Nat
  numIndices : Nat
  numNested : Nat
  all : Array Name
  /-- Constructors: name, type, field count. -/
  ctors : Array (Name × Expr × Nat)
  isUnsafe : Bool
  deriving Inhabited

def IndView.ofConst? (const? : Name → Option ConstantInfo) (n : Name) : Option IndView :=
  match const? n with
  | some (.inductInfo v) =>
    let ctors := v.ctors.filterMap fun c =>
      match const? c with
      | some (.ctorInfo cv) => some (c, cv.cnst.type, cv.numFields)
      | _ => none
    some { name := n, levelParams := v.cnst.levelParams, type := v.cnst.type,
           numParams := v.numParams, numIndices := v.numIndices,
           numNested := v.numNested, all := v.all, ctors, isUnsafe := v.isUnsafe }
  | _ => none

/-! ## Expansion -/

inductive Dedup where
  /-- Historical trigger-only compiler policy: only the triggering
  occurrence, keyed to the first auxiliary of the group. Kept as a model
  variant; current production iterates every class member. -/
  | compiler
  /-- Lean's kernel: every member of the new group. -/
  | lean
  deriving BEq, Repr, Inhabited

structure XCtor where
  name : Name
  typ : Expr
  nFields : Nat
  deriving Inhabited

structure XMember where
  name : Name
  /-- The source member whose constructor walk discovered this member. -/
  sourceOwner : Name
  typ : Expr
  ctors : Array XCtor
  nParams : Nat
  nIndices : Nat
  deriving Inhabited

/-- An expanded block: the members first, then the auxiliaries in discovery
order. -/
structure Expanded where
  types : Array XMember
  /-- Auxiliary ↦ its occurrence `J.{ls} Ds`, `Ds` at depth 0. -/
  auxToNested : NameTable Expr
  auxCtorMap : NameTable (Name × Name)
  nOriginals : Nat
  levelParams : Array Name
  nParams : Nat
  /-- Original block anchor and exact source protection for any later auxiliary ordering. -/
  all0 : Name := default
  sourceNames : List Lean.Name := []
  deriving Inhabited

def Expanded.aux (x : Expanded) : Array XMember := x.types.extract x.nOriginals x.types.size

/-- The external group a new occurrence of `I` opens, as classes in order
(each class's first name is its representative, which gets the auxiliary;
every name of the class is registered as seen). Lean's kernel opens `I.all`
(`leanSourceGroup`). Over a canonical block the group is `I`'s canonical
component instead, which is what the kernels can recompute from Ixon (the
compiler passes its compiled classes); the two agree whenever `I`'s block is
an identity block. -/
structure SourceGroups where
  blocks : Std.HashMap Name (Array (Array Name)) := {}
  deriving Inhabited

/-- The canonical group from a compiled class registry (the compiler's
`CompileEnv.blocks` / Rust `stt.blocks`: each member's block classes in
canonical order, representative first); `I.all` for a block the registry
does not hold. -/
def blockGroup (blocks : Std.HashMap Name (Array (Array Name))) (name : Name)
    (all : Array Name) : Array (Array Name) :=
  match blocks.get? name with
  | some classes => classes.filter (!·.isEmpty)
  | none => all.map (#[·])

@[inherit_doc blockGroup]
def SourceGroups.apply (groups : SourceGroups) (v : IndView) : Array (Array Name) :=
  blockGroup groups.blocks v.name v.all

instance : CoeFun SourceGroups (fun _ => IndView → Array (Array Name)) := ⟨SourceGroups.apply⟩

/-- Lean's group: the recorded `I.all`, with no compiled registry override. -/
def leanSourceGroup : SourceGroups := {}

def sourceGroupsOfBlocks (blocks : Std.HashMap Name (Array (Array Name))) : SourceGroups := ⟨blocks⟩

/-- The original unrestricted group callback. No finite registry or completeness
proof is required of a generic caller. -/
abbrev GroupOf := IndView → Array (Array Name)

/-- Lean's source grouping, with each recorded member its own class. -/
def leanGroup : GroupOf := leanSourceGroup.apply

/-- The original registry-to-callback API, with no restriction on other callbacks. -/
def groupOfBlocks (blocks : Std.HashMap Name (Array (Array Name))) : GroupOf :=
  (sourceGroupsOfBlocks blocks).apply

/-- Reconstruct a canonical positional universe using the block's original
parameter names. An invalid position is an explicit error, never a fallback
level. -/
def keyLevelOfUniv (ctx : List Name) : Ixon.Univ → Except String Level
  | .zero => pure Level.mkZero
  | .succ u => Level.mkSucc <$> keyLevelOfUniv ctx u
  | .max u v => Level.mkMax <$> keyLevelOfUniv ctx u <*> keyLevelOfUniv ctx v
  | .imax u v => Level.mkIMax <$> keyLevelOfUniv ctx u <*> keyLevelOfUniv ctx v
  | .var i => match ctx[i.toNat]? with
    | some n => pure (Level.mkParam n)
    | none => .error s!"nested key: universe position {i} outside block context"

/-- The serializer's universe normal form, with parameters kept distinct by
position. Only the occurrence key uses this form; original level spellings
remain in the expansion and its metadata. -/
def keyLevel (ctx : List Name) (u : Level) : Except String Level := do
  keyLevelOfUniv ctx (Ixon.canonUniv (← toUniv ctx u))

/-- Reference identities remain typed: an external address is never encoded
as an ordinary source name. Missing addresses retain the source identity. -/
def addrRef (addr? : Name → Option Address) (keep : Name → Bool) (n : Name) : OccurrenceRef :=
  if keep n then .named (keyName n) else match addr? n with
    | some a => .external a
    | none => .named (keyName n)

/-- The canonical nested occurrence key. Resolved external references are
address-tagged; source/generated names retain a distinct tag. Universes use
exactly the serializer's positional normal form. Binder annotations and
metadata are erased only in this canonical key. -/
def addrKey (ctx : List Name) (addr? : Name → Option Address)
    (keep : Name → Bool) : Expr → Except String OccurrenceKey
  | .sort u _ => (OccurrenceKey.sort ∘ keyLevelShape) <$> keyLevel ctx u
  | .const n ls _ => do
    pure (.const (addrRef addr? keep n) ((← ls.mapM (keyLevel ctx)).toList.map keyLevelShape))
  | .app f a _ => OccurrenceKey.app <$> addrKey ctx addr? keep f <*> addrKey ctx addr? keep a
  | .lam _ t b _ _ => do
    pure (.lam .anonymous (← addrKey ctx addr? keep t) (← addrKey ctx addr? keep b) 0)
  | .forallE _ t b _ _ => do
    pure (.forallE .anonymous (← addrKey ctx addr? keep t) (← addrKey ctx addr? keep b) 0)
  | .letE _ t v b nd _ => do
    pure (.letE .anonymous (← addrKey ctx addr? keep t)
      (← addrKey ctx addr? keep v) (← addrKey ctx addr? keep b) nd)
  | .proj n i s _ => do
    pure (.proj (addrRef addr? keep n) i (← addrKey ctx addr? keep s))
  | .mdata _ x _ => addrKey ctx addr? keep x
  | e => pure (occurrenceKey e)

/-- The raw expression digest is only a candidate bucket; confirmed structural
lookup handles equal canonical keys with different raw names or levels. -/
def addrOccurrence (ctx : List Name) (addr? : Name → Option Address)
    (keep : Name → Bool) (e : Expr) : Except String OccurrenceInput :=
  (fun key => ⟨key, hash e⟩) <$> addrKey ctx addr? keep e

structure XCtx where
  source : Ix.Environment := { consts := {} }
  sourceMembers : Array Name := #[]
  ind? : Name → Option IndView
  groupOf : SourceGroups := leanSourceGroup
  /-- Deduplicate occurrences up to compiled addresses (`addrKey`): the
  canonical expansion. `none` for Lean's source walk. -/
  keyAddr? : Option (Name → Option Address) := none
  dedup : Dedup
  all0 : Name
  blockLevels : Array Level
  levelParams : List Name := []
  nParams : Nat
  paramBinders : Array Binder

structure XSt where
  types : Array XMember := #[]
  typeNames : NameSet := {}
  auxToNested : NameTable Expr := {}
  auxCtorMap : NameTable (Name × Name) := {}
  seen : OccurrenceTable := {}
  /-- A malformed canonical key is reported by the queue driver. -/
  keyError : Option String := none
  nextAuxIdx : Nat := 1
  /-- Computed once, on the first auxiliary allocation. -/
  sourceNames? : Option (List Lean.Name) := none
  allocatedNames : List Lean.Name := []
  allocatedCtorRoots : List Lean.Name := []
  deriving Inhabited

/-- Lazily collect actual block-reachable source names. Non-nested blocks do not traverse it. -/
def XSt.sourceNames (cx : XCtx) (st : XSt) : List Lean.Name :=
  match st.sourceNames? with
  | some names => names
  | none => (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames

def XSt.push (st : XSt) (m : XMember) : XSt :=
  { st with types := st.types.push m, typeNames := st.typeNames.insert m.name () }

/-- Rewrite the result `J Ds is` of an auxiliary constructor to
`aux params is` (`replaceCtorResultHeadWithAux`); `depth` counts the binders
passed. -/
def replaceCtorResultHead (jName auxName : Name) (extNParams : Nat)
    (blockLevels : Array Level) (nParams : Nat) : Expr → Nat → Expr
  | .forallE n t b bi _, d =>
    Expr.mkForallE n t (replaceCtorResultHead jName auxName extNParams blockLevels nParams b (d + 1)) bi
  | .mdata md x _, d =>
    Expr.mkMData md (replaceCtorResultHead jName auxName extNParams blockLevels nParams x d)
  | e, d =>
    let (h, args) := getAppFnArgs e
    match h with
    | .const hn _ _ =>
      if hn != jName || args.size < extNParams then e
      else
        let ps := (Array.range nParams).map fun i => Expr.mkBVar (d + nParams - 1 - i)
        mkAppN (mkAppN (Expr.mkConst auxName blockLevels) ps)
          (args.extract extNParams args.size)
    | _ => e

/-- The block parameters at depth `d`, as arguments. -/
def paramArgs (np d : Nat) : Array Expr :=
  (Array.range np).map fun i => Expr.mkBVar (d + np - 1 - i)

/-- Test `e` (at depth `d` below `np` peeled parameters) as a nested
occurrence; on a new one, append its group. -/
def replaceIfNested (cx : XCtx) (np : Nat) (owner : Name) (e : Expr) (d : Nat)
    (st : XSt) : Option Expr × XSt := Id.run do
  let (h, args) := getAppFnArgs e
  let .const hn hls _ := h | return (none, st)
  if st.typeNames.contains hn then return (none, st)
  let some ext := cx.ind? hn | return (none, st)
  let enp := ext.numParams
  if args.size < enp then return (none, st)
  let ps := args.extract 0 enp
  if !ps.any (mentionsName st.typeNames.contains) then return (none, st)
  if !ps.all (looseAtLeast · d) then return (none, st)
  let specs := ps.map (lowerLoose · d)
  let iAs := mkAppN (Expr.mkConst hn hls) specs
  let repl := fun (aux : Name) =>
    mkAppN (mkAppN (Expr.mkConst aux cx.blockLevels) (paramArgs np d))
      (args.extract enp args.size)
  let names := st.typeNames
  let keyOf := fun (x : Expr) => match cx.keyAddr? with
    | some f => addrOccurrence cx.levelParams f names.contains x
    | none => .ok (sourceOccurrence x)
  match keyOf iAs with
  | .error e => return (none, { st with keyError := st.keyError.or (some e) })
  | .ok key =>
    if let some aux := st.seen.get? key then return (some (repl aux), st)
    let mut st := st
    let mut result : Option Expr := none
    for cls in cx.groupOf ext do
      let some jName := cls[0]? | continue
      let some j := cx.ind? jName | continue
      let sourceNames := st.sourceNames cx
      let forbidden := st.allocatedNames ++ sourceNames
      let auxName := freshFamily forbidden (Name.mkStr cx.all0 "_nested")
        s!"{(namePretty jName).replace "." "_"}_{st.nextAuxIdx}"
      let jAs := mkAppN (Expr.mkConst jName hls) specs
      st := { st with
        nextAuxIdx := st.nextAuxIdx + 1
        sourceNames? := some sourceNames
        allocatedNames := keyName auxName :: st.allocatedNames
        auxToNested := st.auxToNested.insert auxName jAs }
      st := match cx.dedup with
        | .compiler => if st.seen.contains iAs then st else { st with seen := st.seen.insert iAs auxName }
        | .lean => cls.foldl (init := st) fun st k =>
            match keyOf (mkAppN (Expr.mkConst k hls) specs) with
            | .error e => { st with keyError := st.keyError.or (some e) }
            | .ok kAs =>
              if st.seen.contains kAs then st else { st with seen := st.seen.insert kAs auxName }
      let jType := instantiatePiParams (substLevels j.levelParams hls j.type) enp specs
      let auxType := mkForalls cx.paramBinders jType
      let mut ctors : Array XCtor := #[]
      for (cn, ct, nf) in j.ctors do
        let candidate := nameReplacePrefix cn jName auxName
        let auxCtorName := freshCtorFamily (st.allocatedNames ++ sourceNames) auxName candidate ctors.size st.allocatedCtorRoots
        let t := instantiatePiParams (substLevels j.levelParams hls ct) enp specs
        let t := replaceCtorResultHead jName auxName enp cx.blockLevels cx.nParams t 0
        st := { st with
          auxCtorMap := st.auxCtorMap.insert auxCtorName (cn, auxName)
          allocatedNames := keyName auxCtorName :: st.allocatedNames
          allocatedCtorRoots := keyName auxCtorName :: st.allocatedCtorRoots }
        ctors := ctors.push { name := auxCtorName, typ := mkForalls cx.paramBinders t, nFields := nf }
      if cls.contains hn then result := some (repl auxName)
      st := st.push { name := auxName, sourceOwner := owner, typ := auxType, ctors,
                      nParams := cx.nParams, nIndices := j.numIndices }
    return (result, st)

/-- Lean's `replace` with `replaceIfNested`, pre-order. -/
def replaceAll (cx : XCtx) (np : Nat) (owner : Name) : Expr → Nat → XSt → Expr × XSt
  | e, d, st =>
    match replaceIfNested cx np owner e d st with
    | (some r, st) => (r, st)
    | (none, st) =>
      match e with
      | .app f a _ =>
        let (f', st) := replaceAll cx np owner f d st
        let (a', st) := replaceAll cx np owner a d st
        (Expr.mkApp f' a', st)
      | .lam n t b bi _ =>
        let (t', st) := replaceAll cx np owner t d st
        let (b', st) := replaceAll cx np owner b (d + 1) st
        (Expr.mkLam n t' b' bi, st)
      | .forallE n t b bi _ =>
        let (t', st) := replaceAll cx np owner t d st
        let (b', st) := replaceAll cx np owner b (d + 1) st
        (Expr.mkForallE n t' b' bi, st)
      | .letE n t v b nd _ =>
        let (t', st) := replaceAll cx np owner t d st
        let (v', st) := replaceAll cx np owner v d st
        let (b', st) := replaceAll cx np owner b (d + 1) st
        (Expr.mkLetE n t' v' b' nd, st)
      | .proj n i s _ =>
        let (s', st) := replaceAll cx np owner s d st
        (Expr.mkProj n i s', st)
      | .mdata md x _ =>
        let (x', st) := replaceAll cx np owner x d st
        (Expr.mkMData md x', st)
      | _ => (e, st)

/-- Process constructor `ci` of queue member `qi`. -/
def walkCtor (cx : XCtx) (qi ci : Nat) (st : XSt) : XSt :=
  match st.types[qi]? with
  | none => st
  | some mem =>
    match mem.ctors[ci]? with
    | none => st
    | some c =>
      let (bs, body) := peelForalls cx.nParams c.typ #[]
      let (body', st) := replaceAll cx bs.size mem.sourceOwner body 0 st
      let typ := mkForalls bs body'
      { st with types := st.types.modify qi fun m =>
          { m with ctors := m.ctors.modify ci fun c => { c with typ } } }

/-- The queue loop; the fuel bounds the number of members. -/
def walkQueue (cx : XCtx) : Nat → Nat → XSt → Except String XSt
  | 0, qi, st =>
    match st.keyError with
    | some e => .error e
    | none => if qi < st.types.size then .error "nested expansion: auxiliary bound exceeded" else pure st
  | fuel + 1, qi, st =>
    match st.keyError with
    | some e => .error e
    | none =>
      match st.types[qi]? with
      | none => pure st
      | some mem =>
        let st := (List.range mem.ctors.size).foldl (fun st ci => walkCtor cx qi ci st) st
        walkQueue cx fuel (qi + 1) st

/-- Maximum members of an expanded block. -/
def expansionBound : Nat := 100000

/-- Expand the block whose members are `ordered` (in that order), with
collapsed members renamed by `aliasToRep` first (`expandNestedBlock`). -/
def expandSourceSpec (source : Ix.Environment) (dedup : Dedup) (ordered : Array Name)
    (aliasToRep : Std.HashMap Name Name := {}) (groupOf : SourceGroups := leanSourceGroup)
    (keyAddr? : Option (Name → Option Address) := none) :
    Except String Expanded := do
  let ind? := IndView.ofConst? source.get?
  let some first := ordered[0]? | .error "expand: empty block"
  let some fi := ind? first | .error s!"expand: {namePretty first} is not an inductive"
  let nParams := fi.numParams
  let (paramBinders, _) := peelForalls nParams fi.type #[]
  let cx : XCtx := { source, sourceMembers := ordered, ind?, groupOf, keyAddr?, dedup, all0 := fi.all[0]?.getD first,
                     blockLevels := fi.levelParams.map Level.mkParam,
                     levelParams := fi.levelParams.toList, nParams, paramBinders }
  let mut st : XSt := {}
  for n in ordered do
    let some v := ind? n | .error s!"expand: {namePretty n} is not an inductive"
    let ctors := v.ctors.map fun (cn, ct, nf) =>
      { name := cn, typ := canonicalizeConstNames aliasToRep ct, nFields := nf : XCtor }
    st := st.push { name := n, sourceOwner := n, typ := canonicalizeConstNames aliasToRep v.type,
                    ctors, nParams, nIndices := v.numIndices }
  let nOriginals := st.types.size
  let fin ← walkQueue cx expansionBound 0 st
  return { types := fin.types, auxToNested := fin.auxToNested, auxCtorMap := fin.auxCtorMap,
           nOriginals, levelParams := fi.levelParams, nParams,
           all0 := cx.all0, sourceNames := fin.sourceNames?.getD [] }

/-! ## Callback-generic expansion core

The finite source wrapper above remains byte-for-byte unchanged during this
additive extraction. `ExpansionCore` keeps arbitrary view/group callbacks and
receives the real wrapper's finite protection as a lazy pure thunk. Its generic
discovery/ownership laws impose no completeness or freshness premise. The
separate `CoreBridge` proof compares complete results with the existing wrapper.
-/

namespace ExpansionCore

/-- Every callback accepted by the former generic expansion interface. -/
abbrev GroupCallback := GroupOf

/-- Queue inputs independent of the representation of the source environment.
`protect` is evaluated only on the existing first-allocation cache miss. -/
structure Ctx where
  protect : Unit → List Lean.Name
  ind? : Name → Option IndView
  groupOf : GroupCallback
  keyAddr? : Option (Name → Option Address) := none
  dedup : Dedup
  all0 : Name
  blockLevels : Array Level
  levelParams : List Name := []
  nParams : Nat
  paramBinders : Array Binder

/-- The actual source-backed context supplies its exact computed support.
This adapter neither traverses the closure eagerly nor supplies a support hint. -/
def Ctx.ofSource (cx : XCtx) : Ctx :=
  { protect := fun () => (sourceContext cx.source cx.sourceMembers cx.groupOf.blocks).protectedNames
    ind? := cx.ind?, groupOf := cx.groupOf.apply, keyAddr? := cx.keyAddr?
    dedup := cx.dedup, all0 := cx.all0, blockLevels := cx.blockLevels
    levelParams := cx.levelParams, nParams := cx.nParams, paramBinders := cx.paramBinders }

/-- Keep the existing lazy source-name cache, even for arbitrary core contexts. -/
def sourceNames (cx : Ctx) (st : XSt) : List Lean.Name :=
  match st.sourceNames? with
  | some names => names
  | none => cx.protect ()

/-- Test `e` (at depth `d` below `np` peeled parameters) as a nested
occurrence; on a new one, append its group. -/
def replaceIfNested (cx : Ctx) (np : Nat) (owner : Name) (e : Expr) (d : Nat)
    (st : XSt) : Option Expr × XSt := Id.run do
  let (h, args) := getAppFnArgs e
  let .const hn hls _ := h | return (none, st)
  if st.typeNames.contains hn then return (none, st)
  let some ext := cx.ind? hn | return (none, st)
  let enp := ext.numParams
  if args.size < enp then return (none, st)
  let ps := args.extract 0 enp
  if !ps.any (mentionsName st.typeNames.contains) then return (none, st)
  if !ps.all (looseAtLeast · d) then return (none, st)
  let specs := ps.map (lowerLoose · d)
  let iAs := mkAppN (Expr.mkConst hn hls) specs
  let repl := fun (aux : Name) =>
    mkAppN (mkAppN (Expr.mkConst aux cx.blockLevels) (paramArgs np d))
      (args.extract enp args.size)
  let names := st.typeNames
  let keyOf := fun (x : Expr) => match cx.keyAddr? with
    | some f => addrOccurrence cx.levelParams f names.contains x
    | none => .ok (sourceOccurrence x)
  match keyOf iAs with
  | .error e => return (none, { st with keyError := st.keyError.or (some e) })
  | .ok key =>
    if let some aux := st.seen.get? key then return (some (repl aux), st)
    let mut st := st
    let mut result : Option Expr := none
    for cls in cx.groupOf ext do
      let some jName := cls[0]? | continue
      let some j := cx.ind? jName | continue
      let sourceNames := sourceNames cx st
      let forbidden := st.allocatedNames ++ sourceNames
      let auxName := freshFamily forbidden (Name.mkStr cx.all0 "_nested")
        s!"{(namePretty jName).replace "." "_"}_{st.nextAuxIdx}"
      let jAs := mkAppN (Expr.mkConst jName hls) specs
      st := { st with
        nextAuxIdx := st.nextAuxIdx + 1
        sourceNames? := some sourceNames
        allocatedNames := keyName auxName :: st.allocatedNames
        auxToNested := st.auxToNested.insert auxName jAs }
      st := match cx.dedup with
        | .compiler => if st.seen.contains iAs then st else { st with seen := st.seen.insert iAs auxName }
        | .lean => cls.foldl (init := st) fun st k =>
            match keyOf (mkAppN (Expr.mkConst k hls) specs) with
            | .error e => { st with keyError := st.keyError.or (some e) }
            | .ok kAs =>
              if st.seen.contains kAs then st else { st with seen := st.seen.insert kAs auxName }
      let jType := instantiatePiParams (substLevels j.levelParams hls j.type) enp specs
      let auxType := mkForalls cx.paramBinders jType
      let mut ctors : Array XCtor := #[]
      for (cn, ct, nf) in j.ctors do
        let candidate := nameReplacePrefix cn jName auxName
        let auxCtorName := freshCtorFamily (st.allocatedNames ++ sourceNames) auxName candidate ctors.size st.allocatedCtorRoots
        let t := instantiatePiParams (substLevels j.levelParams hls ct) enp specs
        let t := replaceCtorResultHead jName auxName enp cx.blockLevels cx.nParams t 0
        st := { st with
          auxCtorMap := st.auxCtorMap.insert auxCtorName (cn, auxName)
          allocatedNames := keyName auxCtorName :: st.allocatedNames
          allocatedCtorRoots := keyName auxCtorName :: st.allocatedCtorRoots }
        ctors := ctors.push { name := auxCtorName, typ := mkForalls cx.paramBinders t, nFields := nf }
      if cls.contains hn then result := some (repl auxName)
      st := st.push { name := auxName, sourceOwner := owner, typ := auxType, ctors,
                      nParams := cx.nParams, nIndices := j.numIndices }
    return (result, st)

/-- Lean's `replace` with `replaceIfNested`, pre-order. -/
def replaceAll (cx : Ctx) (np : Nat) (owner : Name) : Expr → Nat → XSt → Expr × XSt
  | e, d, st =>
    match replaceIfNested cx np owner e d st with
    | (some r, st) => (r, st)
    | (none, st) =>
      match e with
      | .app f a _ =>
        let (f', st) := replaceAll cx np owner f d st
        let (a', st) := replaceAll cx np owner a d st
        (Expr.mkApp f' a', st)
      | .lam n t b bi _ =>
        let (t', st) := replaceAll cx np owner t d st
        let (b', st) := replaceAll cx np owner b (d + 1) st
        (Expr.mkLam n t' b' bi, st)
      | .forallE n t b bi _ =>
        let (t', st) := replaceAll cx np owner t d st
        let (b', st) := replaceAll cx np owner b (d + 1) st
        (Expr.mkForallE n t' b' bi, st)
      | .letE n t v b nd _ =>
        let (t', st) := replaceAll cx np owner t d st
        let (v', st) := replaceAll cx np owner v d st
        let (b', st) := replaceAll cx np owner b (d + 1) st
        (Expr.mkLetE n t' v' b' nd, st)
      | .proj n i s _ =>
        let (s', st) := replaceAll cx np owner s d st
        (Expr.mkProj n i s', st)
      | .mdata md x _ =>
        let (x', st) := replaceAll cx np owner x d st
        (Expr.mkMData md x', st)
      | _ => (e, st)

/-- Process constructor `ci` of queue member `qi`. -/
def walkCtor (cx : Ctx) (qi ci : Nat) (st : XSt) : XSt :=
  match st.types[qi]? with
  | none => st
  | some mem =>
    match mem.ctors[ci]? with
    | none => st
    | some c =>
      let (bs, body) := peelForalls cx.nParams c.typ #[]
      let (body', st) := replaceAll cx bs.size mem.sourceOwner body 0 st
      let typ := mkForalls bs body'
      { st with types := st.types.modify qi fun m =>
          { m with ctors := m.ctors.modify ci fun c => { c with typ } } }

/-- The queue loop; the fuel bounds the number of members. -/
def walkQueue (cx : Ctx) : Nat → Nat → XSt → Except String XSt
  | 0, qi, st =>
    match st.keyError with
    | some e => .error e
    | none => if qi < st.types.size then .error "nested expansion: auxiliary bound exceeded" else pure st
  | fuel + 1, qi, st =>
    match st.keyError with
    | some e => .error e
    | none =>
      match st.types[qi]? with
      | none => pure st
      | some mem =>
        let st := (List.range mem.ctors.size).foldl (fun st ci => walkCtor cx qi ci st) st
        walkQueue cx fuel (qi + 1) st

/-- Expand the block whose members are `ordered` (in that order), with
collapsed members renamed by `aliasToRep` first (`expandNestedBlock`). -/
def expand (protect : Unit → List Lean.Name) (ind? : Name → Option IndView)
    (dedup : Dedup) (ordered : Array Name)
    (aliasToRep : Std.HashMap Name Name := {}) (groupOf : GroupCallback := fun v => v.all.map (#[·]))
    (keyAddr? : Option (Name → Option Address) := none) :
    Except String Expanded := do
  let some first := ordered[0]? | .error "expand: empty block"
  let some fi := ind? first | .error s!"expand: {namePretty first} is not an inductive"
  let nParams := fi.numParams
  let (paramBinders, _) := peelForalls nParams fi.type #[]
  let cx : Ctx := { protect, ind?, groupOf, keyAddr?, dedup, all0 := fi.all[0]?.getD first,
                     blockLevels := fi.levelParams.map Level.mkParam,
                     levelParams := fi.levelParams.toList, nParams, paramBinders }
  let mut st : XSt := {}
  for n in ordered do
    let some v := ind? n | .error s!"expand: {namePretty n} is not an inductive"
    let ctors := v.ctors.map fun (cn, ct, nf) =>
      { name := cn, typ := canonicalizeConstNames aliasToRep ct, nFields := nf : XCtor }
    st := st.push { name := n, sourceOwner := n, typ := canonicalizeConstNames aliasToRep v.type,
                    ctors, nParams, nIndices := v.numIndices }
  let nOriginals := st.types.size
  let fin ← walkQueue cx expansionBound 0 st
  return { types := fin.types, auxToNested := fin.auxToNested, auxCtorMap := fin.auxCtorMap,
           nOriginals, levelParams := fi.levelParams, nParams,
           all0 := cx.all0, sourceNames := fin.sourceNames?.getD [] }

end ExpansionCore

/-- Public expansion over arbitrary callbacks. Protection is fixed executable
data; the allocator consumes it lazily on the existing first-miss path. -/
def expand (ind? : Name → Option IndView) (dedup : Dedup)
    (ordered : Array Name) (aliases : Std.HashMap Name Name := {})
    (groupOf : GroupOf := leanGroup)
    (keyAddr? : Option (Name → Option Address) := none)
    (protect : Unit → List Lean.Name := fun () => []) : Except String Expanded :=
  ExpansionCore.expand protect ind? dedup ordered aliases groupOf keyAddr?

/-- The actual source producer supplies the exact block-reachable protection
from its source and group registry. The old finite body remains expandSourceSpec
for full-result comparison, including every refusal. -/
def expandSource (source : Ix.Environment) (dedup : Dedup)
    (ordered : Array Name) (aliases : Std.HashMap Name Name := {})
    (groups : SourceGroups := leanSourceGroup)
    (keyAddr? : Option (Name → Option Address) := none) : Except String Expanded :=
  expand (IndView.ofConst? source.get?) dedup ordered aliases groups.apply keyAddr?
    (fun () => (sourceContext source ordered groups.blocks).protectedNames)

/-! ## Signatures -/

/-- An auxiliary's identity: owner, external head, levels, parameters. -/
structure Sig where
  owner : Name
  head : Name
  levels : Array Level
  specs : Array Expr
  deriving Inhabited

def sigOf (x : Expanded) (m : XMember) : Option Sig := do
  let e ← x.auxToNested.get? m.name
  let (h, args) := getAppFnArgs e
  let .const hn ls _ := h | none
  return { owner := m.sourceOwner, head := hn, levels := ls, specs := args }

def Expanded.sigs (x : Expanded) : Array Sig := x.aux.filterMap (sigOf x)

/-- Equality of occurrence parameters (`auxSpecEq`): `mdata` ignored,
levels up to `levelAlphaEq`, constants equal by name, or by compiled address
unless one of them is in `strict`. -/
def auxSpecEq (addr? : Name → Option Address) (strict : Std.HashSet Name) (a b : Expr) : Bool :=
  match a, b with
  | .mdata _ x _, y => auxSpecEq addr? strict x y
  | x, .mdata _ y _ => auxSpecEq addr? strict x y
  | .bvar i _, .bvar j _ => i == j
  | .fvar i _, .fvar j _ => i == j
  | .sort u _, .sort v _ => levelAlphaEq u v
  | .const an als _, .const bn bls _ =>
    als.size == bls.size && (als.zip bls).all (fun (x, y) => levelAlphaEq x y) &&
      (an == bn || (!strict.contains an && !strict.contains bn &&
        match addr? an, addr? bn with
        | some x, some y => x == y
        | _, _ => false))
  | .app f x _, .app g y _ => auxSpecEq addr? strict f g && auxSpecEq addr? strict x y
  | .lam _ t x _ _, .lam _ u y _ _ => auxSpecEq addr? strict t u && auxSpecEq addr? strict x y
  | .forallE _ t x _ _, .forallE _ u y _ _ => auxSpecEq addr? strict t u && auxSpecEq addr? strict x y
  | .letE _ t v x _ _, .letE _ u w y _ _ =>
    auxSpecEq addr? strict t u && auxSpecEq addr? strict v w && auxSpecEq addr? strict x y
  | .proj an ai x _, .proj bn bi y _ =>
    ai == bi && (an == bn || (!strict.contains an && !strict.contains bn &&
        match addr? an, addr? bn with
        | some p, some q => p == q
        | _, _ => false)) && auxSpecEq addr? strict x y
  | .lit x _, .lit y _ => x == y
  | _, _ => false
termination_by exprSize a + exprSize b
decreasing_by
  all_goals simp only [exprSize_app, exprSize_lam, exprSize_forallE,
    exprSize_letE, exprSize_proj, exprSize_mdata]
  all_goals omega

/-- Match `src` (parameters already renamed to the canonical view) against
`canon`: exact levels first, then any levels (`matchAuxSignature`). -/
def matchSig (addr? : Name → Option Address) (strict : Std.HashSet Name)
    (canon : Array Sig) (head : Name) (levels : Array Level) (specs : Array Expr) : Option Nat :=
  -- A7 (D8): the candidates carry their signature (no `canon[i]!`).
  let cands := (canon.zipIdx.filter fun (s, _) => s.head == head).toList
  let eqSpecs := fun (s : Sig) =>
    s.specs.size == specs.size &&
      (s.specs.zip specs).all fun (x, y) => auxSpecEq addr? strict x y
  match cands.find? (fun (s, _) => s.levels == levels && eqSpecs s) with
  | some (_, i) => some i
  | none => (cands.find? fun (s, _) => eqSpecs s).map (·.2)

/-- Some constant (not projection name) of `e` is a block member outside the
component. -/
def mentionsOutside (originals inComp : Std.HashSet Name) (e : Expr) : Bool :=
  let names := originals.fold (init := ({} : Std.HashSet Name)) fun s n =>
    if inComp.contains n then s else s.insert n
  go names e
where
  go (names : Std.HashSet Name) : Expr → Bool
    | .const n _ _ => names.contains n
    | .app f a _ => go names f || go names a
    | .lam _ t b _ _ | .forallE _ t b _ _ => go names t || go names b
    | .letE _ t v b _ _ => go names t || go names v || go names b
    | .proj _ _ s _ | .mdata _ s _ => go names s
    | _ => false

/-- `perm[j]` for each source position `j` (`computeAuxPerm`). `origToCanon`
maps every member of the component to its class representative. -/
def computePerm (addr? : Name → Option Address) (canon : Array Sig) (source : Array Sig)
    (originalAll : Array Name) (origToCanon : Std.HashMap Name Name) :
    Except String (Array (Option Nat)) := do
  let originals : Std.HashSet Name := originalAll.foldl (·.insert ·) {}
  let inComp : Std.HashSet Name := origToCanon.fold (fun s k _ => s.insert k) {}
  let strict : Std.HashSet Name := originalAll.foldl (init := {}) fun s n =>
    if inComp.contains n then s else s.insert n
  let mut perm : Array (Option Nat) := #[]
  for (s, j) in source.zipIdx do
    let specs := s.specs.map (replaceConstNames origToCanon)
    -- an exact spelling first (constants by name), then up to addresses: in
    -- a canonical expansion (deduplicated up to addresses) at most one
    -- candidate matches either way, but an expansion of uncollapsed classes
    -- can hold two candidates equal up to addresses, and each source
    -- position keeps its own (A2-order; Rust `compute_aux_perm`)
    let exact := matchSig (fun _ => none) strict canon s.head s.levels specs
    match exact <|> matchSig addr? strict canon s.head s.levels specs with
    | some i => perm := perm.push (some i)
    | none =>
      if s.specs.any (mentionsOutside originals inComp) || !inComp.contains s.owner then
        perm := perm.push none
      else
        throw s!"computePerm: no canonical match for in-component source auxiliary #{j} \
          (head {namePretty s.head}, owner {namePretty s.owner})"
  for i in [0:canon.size] do
    if !perm.contains (some i) then
      throw s!"computePerm: canonical auxiliary #{i} has no source mapping"
  return perm

/-! ## Today's structural order -/

/-- The marker constructor's type: the occurrence with block parameter `i`
replaced by the literal `bvar i` at every depth (the compiler's
`replaceParamsExpr nested blockParamFvars blockParamBvars`). -/
def markerize (np : Nat) : Expr → Nat → Expr
  | .bvar b _, k =>
    if b ≥ k && b - k < np then Expr.mkBVar (np - 1 - (b - k)) else Expr.mkBVar b
  | .app f a _, k => Expr.mkApp (markerize np f k) (markerize np a k)
  | .lam n t b bi _, k => Expr.mkLam n (markerize np t k) (markerize np b (k + 1)) bi
  | .forallE n t b bi _, k => Expr.mkForallE n (markerize np t k) (markerize np b (k + 1)) bi
  | .letE n t v b nd _, k =>
    Expr.mkLetE n (markerize np t k) (markerize np v k) (markerize np b (k + 1)) nd
  | .proj n i s _, k => Expr.mkProj n i (markerize np s k)
  | .mdata md x _, k => Expr.mkMData md (markerize np x k)
  | e, _ => e

/-- The auxiliaries as the inductives the compiler sorts
(`sortAuxByPartitionRefinement`). -/
def auxMutConsts (x : Expanded) : Array MutConst :=
  x.aux.map fun mem =>
    let ctors := mem.ctors.zipIdx.map fun (c, ci) =>
      ({ cnst := { name := c.name, levelParams := x.levelParams, type := c.typ }
         induct := mem.name, cidx := ci, numParams := mem.nParams,
         numFields := c.nFields, isUnsafe := false } : ConstructorVal)
    let ctors := match x.auxToNested.get? mem.name with
      | some nested => ctors.push
          { cnst := { name := Name.mkStr mem.name "_nested_id", levelParams := x.levelParams,
                      type := markerize x.nParams nested 0 }
            induct := mem.name, cidx := ctors.size, numParams := mem.nParams,
            numFields := 0, isUnsafe := false }
      | none => ctors
    .indc { name := mem.name, levelParams := x.levelParams, type := mem.typ,
            numParams := mem.nParams, numIndices := mem.nIndices, all := #[],
            ctors, numNested := 0, isRec := false, isReflexive := false, isUnsafe := false }

/-- The rules of today's structural auxiliary sort: today's comparator,
with the port fixes as `rules` sets them (`Rules.compiler` turns them on;
they change no result, see `Order.lean`). The seed, levels and tie-break of
`rules` do not apply: the structural order is today's by definition. -/
def Rules.structuralAux (rules : Rules) : Rules :=
  { Rules.today with portFixes := rules.portFixes }

/-- Today's structural order of the auxiliaries of an expansion: their
classes, in order, under `rules.structuralAux`
(`sortAuxByPartitionRefinement` reads this). -/
def structuralAuxClasses (rules : Rules) (addr? : Name → Option Address) (x : Expanded) :
    Except String (List (List MutConst)) :=
  (·.1) <$> sortClasses rules.structuralAux addr? (auxMutConsts x).toList

/-- Canonical auxiliary order of an expansion: the auxiliaries' names, one
per class, in order. Today: sorted structurally (`structuralAuxClasses`);
Phase A: the expansion's own discovery order. Also returns whether the
structural order needs addresses (it differs from the blind sort). -/
def canonicalAuxOrder (rules : Rules) (addr? : Name → Option Address) (x : Expanded) :
    Except String (Array (Array Name) × Bool) := do
  match rules.nested with
  | .discovery => return (x.aux.map fun m => #[m.name], false)
  | .structural =>
    let classes ← structuralAuxClasses rules addr? x
    let blind ← sortClassesBlind rules.structuralAux (auxMutConsts x).toList
    return (classNames classes, classNames classes != classNames blind)

/-- Canonical signatures for an order of class representatives. -/
def sigsInOrder (x : Expanded) (order : Array (Array Name)) : Except String (Array Sig) :=
  order.mapM fun cls => do
    let some rep := cls[0]? | throw "empty auxiliary class"
    let some m := x.aux.find? (·.name == rep) | throw "unknown auxiliary"
    let some s := sigOf x m | throw "auxiliary without occurrence"
    return s

/-! ## Validation against Lean's `rec_N` -/

/-- The occurrence signature of each of Lean's `all₀.rec_j` (`j = 1, …`):
the head, levels and parameters of the major premise's type, parameters at
depth 0. Stops at the first missing `rec_j`. -/
def recMajorSignatures (const? : Name → Option ConstantInfo) (all0 : Name) (nParams : Nat)
    (count : Nat) : Array (Option (Name × Array Level × Array Expr)) :=
  (Array.range count).map fun j =>
    match const? (Name.mkStr all0 s!"rec_{j + 1}") with
    | some (.recInfo r) =>
      let skip := r.numParams + r.numMotives + r.numMinors + r.numIndices
      let (bs, rest) := peelForalls skip r.cnst.type #[]
      if bs.size != skip then none
      else match stripMdata rest with
        | .forallE _ dom _ _ _ =>
          let (h, args) := getAppFnArgs dom
          match h with
          | .const hn ls _ =>
            let inner := skip - nParams
            let enp := args.size - r.numIndices
            let ps := args.extract 0 enp
            if ps.all (looseAtLeast · inner) then some (hn, ls, ps.map (lowerLoose · inner))
            else none
          | _ => none
        | _ => none
    | _ => none

end Ix.Compile.Canon

end
