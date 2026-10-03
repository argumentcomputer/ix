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

  **One difference between Lean and today's compiler** (`Dedup`): Lean
  records every `J Ds` of the new group as seen (`m_nested_aux` gets one
  entry per `J`); the compiler records only the occurrence `I Ds` that
  triggered the group, and keys it to the group's *first* auxiliary
  (`Ix/AuxGen/Nested.lean` `replaceIfNested`, `auxSeen`; Rust
  `replace_if_nested`). The two agree unless a block nests a non-first
  member of an external mutual group, or nests two members of one; then the
  compiler either creates a second group or replaces `I Ds` by the
  auxiliary of `all₀ I`. `Dedup.compiler` mirrors the compiler,
  `Dedup.lean` the kernel.

  ## Orders

  * `NestedOrder.structural` (today, `sortAuxByPartitionRefinement`): the
    auxiliaries, each with a trailing identity-marker constructor typed by
    its occurrence (block parameters as `bvar i`, literally, as the
    compiler does), are sorted by `Classes.sortClasses` with today's rules;
    references to the block's members are external (by address).
  * `NestedOrder.discovery` (Phase A): the discovery order of the expansion
    of the canonical block (members in canonical order, collapsed members
    renamed to their representatives).

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
  /-- Today's compiler: only the triggering occurrence, keyed to the first
  auxiliary of the group. -/
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
  auxToNested : Std.HashMap Name Expr
  auxCtorMap : Std.HashMap Name (Name × Name)
  nOriginals : Nat
  levelParams : Array Name
  nParams : Nat
  deriving Inhabited

def Expanded.aux (x : Expanded) : Array XMember := x.types.extract x.nOriginals x.types.size

structure XCtx where
  ind? : Name → Option IndView
  dedup : Dedup
  all0 : Name
  blockLevels : Array Level
  nParams : Nat
  paramBinders : Array Binder

structure XSt where
  types : Array XMember := #[]
  typeNames : Std.HashSet Name := {}
  auxToNested : Std.HashMap Name Expr := {}
  auxCtorMap : Std.HashMap Name (Name × Name) := {}
  seen : Std.HashMap Expr Name := {}
  nextAuxIdx : Nat := 1
  deriving Inhabited

def XSt.push (st : XSt) (m : XMember) : XSt :=
  { st with types := st.types.push m, typeNames := st.typeNames.insert m.name }

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
  if !ps.any (mentionsAnyName st.typeNames) then return (none, st)
  if !ps.all (looseAtLeast · d) then return (none, st)
  let specs := ps.map (lowerLoose · d)
  let iAs := mkAppN (Expr.mkConst hn hls) specs
  let repl := fun (aux : Name) =>
    mkAppN (mkAppN (Expr.mkConst aux cx.blockLevels) (paramArgs np d))
      (args.extract enp args.size)
  if let some aux := st.seen.get? iAs then return (some (repl aux), st)
  let mut st := st
  let mut result : Option Expr := none
  for jName in ext.all do
    let some j := cx.ind? jName | continue
    let auxName := Name.mkStr (Name.mkStr cx.all0 "_nested")
      s!"{(namePretty jName).replace "." "_"}_{st.nextAuxIdx}"
    let jAs := mkAppN (Expr.mkConst jName hls) specs
    st := { st with
      nextAuxIdx := st.nextAuxIdx + 1
      auxToNested := st.auxToNested.insert auxName jAs }
    st := match cx.dedup with
      | .compiler => if st.seen.contains iAs then st else { st with seen := st.seen.insert iAs auxName }
      | .lean => if st.seen.contains jAs then st else { st with seen := st.seen.insert jAs auxName }
    let jType := instantiatePiParams (substLevels j.levelParams hls j.type) enp specs
    let auxType := mkForalls cx.paramBinders jType
    let mut ctors : Array XCtor := #[]
    for (cn, ct, nf) in j.ctors do
      let auxCtorName := nameReplacePrefix cn jName auxName
      let t := instantiatePiParams (substLevels j.levelParams hls ct) enp specs
      let t := replaceCtorResultHead jName auxName enp cx.blockLevels cx.nParams t 0
      st := { st with auxCtorMap := st.auxCtorMap.insert auxCtorName (cn, auxName) }
      ctors := ctors.push { name := auxCtorName, typ := mkForalls cx.paramBinders t, nFields := nf }
    if jName == hn then result := some (repl auxName)
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
  | 0, qi, st => if qi < st.types.size then .error "nested expansion: auxiliary bound exceeded" else pure st
  | fuel + 1, qi, st =>
    match st.types[qi]? with
    | none => pure st
    | some mem =>
      let st := (List.range mem.ctors.size).foldl (fun st ci => walkCtor cx qi ci st) st
      walkQueue cx fuel (qi + 1) st

/-- Maximum members of an expanded block. -/
def expansionBound : Nat := 100000

/-- Expand the block whose members are `ordered` (in that order), with
collapsed members renamed by `aliasToRep` first (`expandNestedBlock`). -/
def expand (ind? : Name → Option IndView) (dedup : Dedup) (ordered : Array Name)
    (aliasToRep : Std.HashMap Name Name := {}) : Except String Expanded := do
  let some first := ordered[0]? | .error "expand: empty block"
  let some fi := ind? first | .error s!"expand: {namePretty first} is not an inductive"
  let nParams := fi.numParams
  let (paramBinders, _) := peelForalls nParams fi.type #[]
  let cx : XCtx := { ind?, dedup, all0 := fi.all[0]?.getD first,
                     blockLevels := fi.levelParams.map Level.mkParam, nParams, paramBinders }
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
           nOriginals, levelParams := fi.levelParams, nParams }

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
  let cands := (List.range canon.size).filter fun i => canon[i]!.head == head
  let eqSpecs := fun (i : Nat) =>
    canon[i]!.specs.size == specs.size &&
      (canon[i]!.specs.zip specs).all fun (x, y) => auxSpecEq addr? strict x y
  match cands.find? (fun i => canon[i]!.levels == levels && eqSpecs i) with
  | some i => some i
  | none => cands.find? eqSpecs

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
    match matchSig addr? strict canon s.head s.levels specs with
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

/-- Canonical auxiliary order of an expansion: the auxiliaries' names, one
per class, in order. Today: sorted structurally (classes by
`Rules.today`); Phase A: the expansion's own discovery order. Also returns
whether the structural order needs addresses (it differs from the blind
sort). -/
def canonicalAuxOrder (rules : Rules) (addr? : Name → Option Address) (x : Expanded) :
    Except String (Array (Array Name) × Bool) := do
  match rules.nested with
  | .discovery => return (x.aux.map fun m => #[m.name], false)
  | .structural =>
    let cs := (auxMutConsts x).toList
    let (classes, _) ← sortClasses Rules.today addr? cs
    let blind ← sortClassesBlind Rules.today cs
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
