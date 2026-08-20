module

public import Ix.Tc.Knot
public import Ix.Tc.CanonicalCheck

/-!
Mirror: crates/kernel/src/inductive.rs

Inductive schema validation:
- S3/S3b: mutual peers must share the result universe, parameter count, and
  parameter-domain types (memoized per block via `blockPeerAgreementCache` —
  peer agreement is transitive, so one successful pass covers the block).
- A1: constructor parameter domains agree with the inductive's.
- A2: constructor return type is a *manifest* application of the inductive
  (no whnf at the return-type check — `id I` must not pass), with universe
  args exactly `param 0 … param (lvls-1)`, the first `n_params` args exactly
  the opened parameter fvars (FVar identity), arg count exactly
  `params + indices`, and index args free of block inductives.
- A3: strict positivity (skipped for unsafe inductives), including the
  nested-inductive rule: an external inductive applied to block-mentioning
  parameters recursively checks that external ctor fields are positive in
  the augmented address set; index args must not mention the block.
- A4: field sort levels ≤ the inductive's result level (skipped for Prop).

Also hosted here (check.rs helpers used by both dispatch and validation):
well-scopedness validation, plus `getResultSortLevel`, `isLargeEliminator`,
and `computeKTarget` (the recursor machinery consumes the latter two).

As in Rust's `check_inductive_member`, member validation ends by
triggering recursor generation for the block
(`generateBlockRecursors`, below).
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashSet)

/-- A member of the "flat" mutual block used for recursor generation.
    For non-nested inductives, just the original inductive; for nested
    occurrences (e.g. `Array Syntax` in Syntax's ctor fields) an auxiliary
    entry mirroring the external inductive's structure. -/
structure FlatBlockMember (m : Mode) where
  /-- Original: the inductive's id. Auxiliary: the EXTERNAL inductive's id. -/
  id : KId m
  isAux : Bool
  /-- Original: Var refs to the recursor's shared params. Auxiliary: the
      concrete specialized exprs, in the recursor-param context
      (depth = nRecParams). -/
  specParams : Array (KExpr m)
  ownParams : UInt64
  nIndices : UInt64
  ctors : Array (KId m)
  lvls : UInt64
  /-- Abstract shifted universe args (internal processing). -/
  indUs : Array (KUniv m)
  /-- Universe args from the actual nested occurrence (concrete); same as
      `indUs` for originals. -/
  occurrenceUs : Array (KUniv m)
  deriving Inhabited

/-- One mutually-recursive family active during constructor positivity
    checking. `concreteUs = none` denotes the root declaration's own
    `Param(0), …` universe sequence; nested families retain the concrete
    specialization at which they were encountered. -/
structure PositivityGroup (m : Mode) where
  addrs : Array Address
  params : Array (KExpr m)
  concreteUs : Option (Array (KUniv m))
  deriving Inhabited

/-- Exact identity of one flattened nested-inductive specialization.

Universe arguments are load-bearing: Lean may generate two auxiliaries for
the same external family and term-parameter spine when a phantom universe
parameter differs between occurrences. -/
structure NestedSpecializationKey where
  family : Address
  universes : Array Address
  parameters : Array Address
  deriving BEq, Inhabited

namespace NestedSpecializationKey

/-- Exact flat-block identity of one concrete nested-family application. -/
def ofApplication (family : Address) (universes : Array (KUniv m))
    (parameters : Array (KExpr m)) : NestedSpecializationKey :=
  { family
    universes := universes.map (·.addr)
    parameters := parameters.map (·.addr) }

end NestedSpecializationKey

/-- The exact flat-block key represented by a nested positivity group.
The root group has no concrete specialization and therefore no auxiliary key. -/
def PositivityGroup.nestedSpecializationKey?
    (group : PositivityGroup m) (family : Address) :
    Option NestedSpecializationKey :=
  group.concreteUs.map fun universes =>
    NestedSpecializationKey.ofApplication family universes group.params

/-- The flat-block key of the parameter prefix of one nested application. -/
def nestedApplicationSpecializationKey (family : Address)
    (universes : Array (KUniv m)) (args : Array (KExpr m))
    (nParams : Nat) : NestedSpecializationKey :=
  NestedSpecializationKey.ofApplication family universes
    (args.extract 0 nParams)

instance : Inhabited (GeneratedRecursor m) :=
  ⟨⟨default, 0, 0, 0, 0, 0, false, default, #[]⟩⟩

namespace RecM

/-- Sort by the `KId` order (addr-major) and drop adjacent duplicates —
    the Rust `BTreeSet<KId>` key shape for `recMajorsCache`. -/
def sortedDedupIds (ids : Array (KId m)) : Array (KId m) := Id.run do
  let sorted := ids.qsort fun a b => compare a b == .lt
  let mut out : Array (KId m) := Array.mkEmpty sorted.size
  for id in sorted do
    match out.back? with
    | some last => if compare last id != .eq then out := out.push id
    | none => out := out.push id
  return out

/-- Sum declaration-derived natural-number counts while retaining the UInt64
    representation bound used by serialized metadata and de Bruijn indices. -/
def checkedNatMetadataSum (label : String) (parts : Array Nat) :
    RecM m UInt64 := do
  let total := parts.foldl (· + ·) 0
  if total < UInt64.size then
    return total.toUInt64
  throw (.other s!"{label} metadata sum overflow")

/-- Sum attacker-controlled declaration arities without permitting UInt64
    wraparound. Reducer and recursor-generation paths consume these sums as
    binder/major indices, so the combined value must describe the same layout
    as the individual metadata fields. -/
def checkedMetadataSum (label : String) (parts : Array UInt64) :
    RecM m UInt64 :=
  checkedNatMetadataSum label (parts.map (·.toNat))

/-- Sum of pending universe constructors in the validation worklist. -/
def univWorkSize : List (KUniv m) → Nat
  | [] => 0
  | u :: stack => u.size + univWorkSize stack

/-- Sum of pending expression nodes in the depth-indexed validation
    worklist. The depth annotation does not affect termination. -/
def scopedExprWorkSize : List (KExpr m × UInt64) → Nat
  | [] => 0
  | (e, _) :: stack => e.treeSize + scopedExprWorkSize stack

/-- Peel the syntactic forall prefix used when building a rule IH. This is
    structural: unlike the surrounding reducer-driven telescope scans, no
    WHNF or binder instantiation occurs between iterations. -/
def peelRuleIhForalls (root : KExpr m) (flat : Array (FlatBlockMember m)) :
    Array (KExpr m) × KExpr m :=
  go root #[]
where
  go (inner : KExpr m) (domains : Array (KExpr m)) :
      Array (KExpr m) × KExpr m :=
    match inner with
    | .all _ _ dom body _ =>
      let (head, _) := inner.collectSpine
      let isFlatHead := match head with
        | .const id _ _ => flat.any (·.id.addr == id.addr)
        | _ => false
      if isFlatHead then (domains, inner)
      else go body (domains.push dom)
    | _ => (domains, inner)
  termination_by inner.treeSize
  decreasing_by
    simp [KExpr.treeSize]
    omega

mutual

-- ### Well-scopedness validation (check.rs)

/-- Universe params in range, iterative with an addr-keyed seen set. -/
def validateUnivParamsSeen (root : KUniv m) (bound : Nat)
    (seen : HashSet Address) : RecM m (HashSet Address) :=
  go [root] seen
where
  /-- Head-of-list is the old Array stack's back. -/
  go (stack : List (KUniv m)) (seen : HashSet Address) :
      RecM m (HashSet Address) :=
    match stack with
    | [] => pure seen
    | u :: stack => do
      if seen.contains u.addr then
        return (← go stack seen)
      let seen := seen.insert u.addr
      match u with
      | .zero _ => go stack seen
      | .succ inner _ => go (inner :: stack) seen
      | .max a b _ | .imax a b _ => go (b :: a :: stack) seen
      | .param idx _ _ =>
        if idx.toNat ≥ bound then
          throw (.univParamOutOfRange idx bound)
        go stack seen
  termination_by univWorkSize stack
  decreasing_by
    all_goals simp [univWorkSize, KUniv.size, KUniv.size_pos] <;> omega

/-- Closed at top level; every `param` within the declaration's own level
    arity; const arities match; prj heads known. Iterative, memoized on
    `(addr, depth)`. Mirrors check.rs `validate_expr_well_scoped`. -/
def validateExprWellScoped (root : KExpr m) (rootDepth : UInt64)
    (lvlBound : Nat) : RecM m Unit :=
  go [(root, rootDepth)] {} {}
where
  /-- LIFO order matches the former Array worklist. -/
  go (stack : List (KExpr m × UInt64))
      (seenExprs : HashSet (Address × UInt64))
      (seenUnivs : HashSet Address) : RecM m Unit :=
    match stack with
    | [] => pure ()
    | (e, depth) :: stack => do
      if seenExprs.contains (e.addr, depth) then
        return (← go stack seenExprs seenUnivs)
      let seenExprs := seenExprs.insert (e.addr, depth)
      match e with
      | .var idx _ _ =>
        if idx ≥ depth then
          throw (.varOutOfRange idx depth.toNat)
        go stack seenExprs seenUnivs
      | .sort u _ =>
        let seenUnivs ← validateUnivParamsSeen u lvlBound seenUnivs
        go stack seenExprs seenUnivs
      | .const id us _ =>
        let c ← TcM.getConst id
        if c.lvls.toNat != us.size then
          throw (.univParamMismatch c.lvls us.size)
        let mut seenUnivs := seenUnivs
        for u in us do
          seenUnivs ← validateUnivParamsSeen u lvlBound seenUnivs
        go stack seenExprs seenUnivs
      | .app f a _ =>
        go ((a, depth) :: (f, depth) :: stack) seenExprs seenUnivs
      | .lam _ _ ty body _ | .all _ _ ty body _ =>
        go ((body, depth + 1) :: (ty, depth) :: stack) seenExprs seenUnivs
      | .letE _ ty val body _ _ =>
        go ((body, depth + 1) :: (val, depth) :: (ty, depth) :: stack)
          seenExprs seenUnivs
      | .prj id _ val _ =>
        if !(← TcM.hasConst id) then
          throw (.unknownConst id.addr)
        go ((val, depth) :: stack) seenExprs seenUnivs
      -- FVars carry no de Bruijn index; leaves.
      | .fvar .. | .nat .. | .str .. => go stack seenExprs seenUnivs
  termination_by scopedExprWorkSize stack
  decreasing_by
    all_goals
      simp [scopedExprWorkSize, KExpr.treeSize, KExpr.treeSize_pos] <;> omega

def validateConstWellScoped (c : KConst m) : RecM m Unit := do
  let lvlBound := c.lvls.toNat
  validateExprWellScoped c.ty 0 lvlBound
  match c with
  | .defn (val := val) .. =>
    validateExprWellScoped val 0 lvlBound
  | .recr (rules := rules) .. =>
    for rule in rules do
      validateExprWellScoped rule.rhs 0 lvlBound
  | _ => pure ()

-- ### Sort/eliminator analysis

/-- Result sort after peeling `n` foralls (opened with fresh fvars). -/
def getResultSortLevel (ty : KExpr m) (n : Nat) :
    RecM m (KUniv m) := do
  let saved := (← get).lctx.size
  let mut t := ty
  for i in [0:n] do
    let w ← whnf t
    match w with
    | .all _ _ dom body _ =>
      let (open', _) ← TcM.openBinderAnon dom body
      t := open'
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other s!"get_result_sort_level: expected {n} foralls, only found {i}")
  let w ← whnf t
  let result ← match w with
    | .sort u _ => pure u
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "get_result_sort_level: not a sort")
  modify fun s => { s with lctx := s.lctx.truncate saved }
  return result

/-- Large eliminator (can target any universe): non-Prop, or Empty-like
    (0 ctors), or single-ctor Prop whose non-Prop fields all appear among
    the return-type args (lean4lean `isLargeEliminator`). -/
def isLargeEliminator (resultLevel : KUniv m)
    (indInfos : Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m)) :
    RecM m Bool := do
  -- isNeverZero (not !isZero) so Param(u) falls through to the check below.
  if resultLevel.isNeverZero then
    return true
  if indInfos.size != 1 then
    return false
  let (_, nParams64, _, ctors, _) := indInfos[0]!
  let nParams := nParams64.toNat
  match ctors.size with
  | 0 => return true
  | 1 =>
    let (ctorTy, ctorFields) ← match (← TcM.tryGetConst ctors[0]!) with
      | some (.ctor (ty := ty) (fields := fields) ..) =>
        pure (ty, fields.toNat)
      | _ => return false
    if ctorFields == 0 then
      return true
    let saved := (← get).lctx.size
    let mut ty := ctorTy
    let mut nonTrivial : Array Nat := #[]
    let mut fieldFVars : Array (KExpr m) := Array.mkEmpty ctorFields
    for i in [0:nParams + ctorFields] do
      let w ← whnf ty
      match w with
      | .all _ _ dom body _ =>
        if i ≥ nParams then
          let domTy ← inferOnlyCall dom
          match (← try? (ensureSortDirect domTy)) with
          | some sortLvl =>
            if !univEq sortLvl .mkZero then
              nonTrivial := nonTrivial.push (i - nParams)
          | none => pure ()
        let (open', fv, _) ← TcM.openBinderAnonWithFV dom body
        if i ≥ nParams then
          fieldFVars := fieldFVars.push fv
        ty := open'
      | _ => break
    let (_, retArgs) := ty.collectSpine
    let result := nonTrivial.all fun fi =>
      let target := fieldFVars[fi]!
      retArgs.any fun arg =>
        match arg with
        | .fvar .. => arg.addr == target.addr
        | _ => false
    modify fun s => { s with lctx := s.lctx.truncate saved }
    return result
  | _ => return false

/-- K-like target: single non-mutual inductive, Prop result (semantic zero),
    exactly one constructor with zero non-param fields. -/
def computeKTarget (indId : KId m) : RecM m Bool := do
  let (indParams, indIndices, ctors, block, ty) ←
    match (← TcM.tryGetConst indId) with
    | some (.indc (params := params) (indices := indices) (ctors := ctors)
        (block := block) (ty := ty) ..) =>
      pure (params, indices, ctors, block, ty)
    | _ => return false
  let blockInds ← discoverBlockInductives block
  if blockInds.size != 1 then
    return false
  let indArity ← checkedMetadataSum "inductive params + indices"
    #[indParams, indIndices]
  let resultLevel ← getResultSortLevel ty indArity.toNat
  if !univEq resultLevel .mkZero then
    return false
  if ctors.size != 1 then
    return false
  match (← TcM.tryGetConst ctors[0]!) with
  | some (.ctor (fields := fields) ..) => return fields == 0
  | _ => return false

-- ### A1–A4 constructor validation

/-- A1 / S3b: walk the first `nParams` foralls of both types, def-eq the
    domains, and open both bodies with the SAME fvar. -/
def checkParamAgreement (indTy ctorTy : KExpr m) (nParams : Nat) :
    RecM m Unit := do
  let saved := (← get).lctx.size
  let mut it := indTy
  let mut ct := ctorTy
  for _ in [0:nParams] do
    let wi ← whnf it
    let wc ← whnf ct
    match wi, wc with
    | .all _ _ iDom iBody _, .all _ _ cDom cBody _ =>
      if !(← isDefEq iDom cDom) then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other "param domain mismatch")
      let (iOpen, fv, _) ← TcM.openBinderAnonWithFV iDom iBody
      let cOpen ← TcM.runIntern (instantiateRev cBody #[fv])
      it := iOpen
      ct := cOpen
    | _, _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "expected forall in param agreement")
  modify fun s => { s with lctx := s.lctx.truncate saved }

/-- A3: strict positivity — block inductives must not appear in negative
    position in any constructor field. -/
def checkPositivity (ctorTy : KExpr m) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Unit := do
  let saved := (← get).lctx.size
  let result ←
    try
      -- Open the shared parameter binders so recursive applications can be
      -- compared with stable fvars, including below dependent field binders.
      let mut ty := ctorTy
      let mut paramFVars : Array (KExpr m) := Array.mkEmpty nParams
      for _ in [0:nParams] do
        let w ← whnf ty
        match w with
        | .all _ _ dom body _ =>
          let (open', fv, _) ← TcM.openBinderAnonWithFV dom body
          paramFVars := paramFVars.push fv
          ty := open'
        | _ => return ()
      let groups : Array (PositivityGroup m) :=
        #[{ addrs := blockAddrs, params := paramFVars, concreteUs := none }]
      runBounded (fun ty => do
        let w ← whnf ty
        match w with
        | .all _ _ dom body _ =>
          checkPositivityDomain dom groups blockAddrs
          let (open', _) ← TcM.openBinderAnon dom body
          return .next open'
        | _ => return .done ()) maxWhnfFuel.toNat ty
      pure (Except.ok ())
    catch e => pure (Except.error e)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  match result with
  | .ok () => return ()
  | .error e => throw e

/-- Pure universe-specialization guard shared by recursive-occurrence
    validation and its proof layer.  `none` is the root block's symbolic
    `Param(0), ...` specialization; nested groups retain the concrete
    occurrence universes. -/
def positiveUniverseArgumentsAgree (group : PositivityGroup m)
    (us : Array (KUniv m)) : Bool :=
  match group.concreteUs with
  | some expected =>
    expected.size == us.size &&
      (List.range us.size).all fun i => univEq expected[i]! us[i]!
  | none =>
    (List.range us.size).all fun i =>
      univEq us[i]! (.mkParam i.toUInt64 anonN : KUniv m)

/-- Structurally recursive presentation of the stateful parameter-comparison
    loop.  `index` is the next source position and `remaining` is the exact
    number of comparisons still required. -/
def checkPositiveParametersFrom (id : KId m)
    (args params : Array (KExpr m)) : Nat → Nat → RecM m Unit
  | _, 0 => pure ()
  | index, remaining + 1 => do
      if !(← isDefEq args[index]! params[index]!) then
        throw (.other s!"positivity: recursive occurrence {id} has non-uniform parameter {index}: expected {params[index]!}, got {args[index]!}")
      checkPositiveParametersFrom id args params (index + 1) remaining

/-- The exact stateful parameter-comparison loop used by positivity. Naming
    it separately exposes the successful recursive `isDefEq` trace to E2c
    without changing the production comparison order or diagnostics. -/
def checkPositiveParameters (id : KId m) (args params : Array (KExpr m))
    (nParams : Nat) : RecM m Unit :=
  checkPositiveParametersFrom id args params 0 nParams

/-- Pure root-index guard.  The slice begins exactly after the uniform
    parameter prefix established by `checkPositiveParameters`. -/
def positiveIndicesIndependent (args : Array (KExpr m)) (nParams : Nat)
    (rootAddrs : Array Address) : Bool :=
  (args.extract nParams args.size).all fun index =>
    !exprMentionsAnyAddr index rootAddrs

/-- The stateless prefix of recursive-application validation.  Keeping the
    original error values here makes the production control flow and the E2c
    success characterization share one definition. -/
def checkPositiveRecursiveApplicationPreconditions
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (group : PositivityGroup m) (nParams nIndices lvls : Nat) :
    Except (TcError m) Unit :=
  if args.size = nParams + nIndices then
    if us.size = lvls then
      if positiveUniverseArgumentsAgree group us = true then
        if group.params.size = nParams then
          .ok ()
        else
          .error (.other
            "positivity: recursive occurrence parameter arity disagrees with its family")
      else
        .error (.other
          "positivity: recursive occurrence has non-uniform universe arguments")
    else
      .error (.other
        s!"positivity: recursive occurrence has wrong universe count: expected {lvls}, got {us.size}")
  else
    .error (.other
      s!"positivity: recursive occurrence has wrong argument count: expected {nParams + nIndices}, got {args.size}")

/-- Validate the already-resolved inductive header of an active recursive
    application.  Separating the lookup/match from these guards gives E2c an
    exact successful-branch seam while preserving their production order. -/
def checkPositiveRecursiveApplicationHeader (id : KId m)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (group : PositivityGroup m) (rootAddrs : Array Address)
    (nParams nIndices lvls : Nat) : RecM m Unit := do
  match checkPositiveRecursiveApplicationPreconditions us args group nParams
      nIndices lvls with
  | .error err => throw err
  | .ok () =>
    checkPositiveParameters id args group.params nParams
    if !positiveIndicesIndependent args nParams rootAddrs then
      throw (.other "positivity: recursive occurrence index mentions an active inductive")

/-- Validate an application of an active recursive family: exact application
    arity, uniform universe/parameter specialization, and index independence. -/
def checkPositiveRecursiveApplication (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs : Array Address) : RecM m Unit := do
  let some group := groups.find? (fun group => group.addrs.contains id.addr)
    | throw (.other "positivity: missing recursive-family context")
  match (← TcM.getConst id) with
  | .indc (params := params) (indices := indices) (lvls := lvls) .. =>
    checkPositiveRecursiveApplicationHeader id us args group rootAddrs
      params.toNat indices.toNat lvls.toNat
  | _ => throw (.other "positivity: recursive head is not an inductive")

/-- Test exact nested-family specialization. The same external inductive may
    have multiple active groups when flattening discovers it at distinct
    parameter specializations. -/
def positivityGroupMatches (group : PositivityGroup m) (family : Address)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (nParams : Nat) : Bool :=
  group.params.size == nParams &&
    group.nestedSpecializationKey? family ==
      some (nestedApplicationSpecializationKey family us args nParams)

/-- Field-domain positivity: recurse through foralls (negative-position
    mentions reject), then require either a direct block-inductive
    application or a valid nested-inductive application (recursively
    checked with the augmented address set). -/
def checkPositivityDomain (dom : KExpr m)
    (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) : RecM m Unit :=
  checkPositivityDomainFuel maxWhnfFuel.toNat dom groups activeAddrs

/-- Explicit call-depth bound for nested positivity. The old mutual recursion
    had no termination guard; exhausting this adversarial-input bound is the
    same local-loop failure used by bounded reduction. Sibling fields reuse
    the bound, so this measures nesting depth rather than total work. -/
def checkPositivityDomainFuel :
    Nat → KExpr m → Array (PositivityGroup m) → Array Address → RecM m Unit
  | 0, _, _, _ => throw .maxRecDepth
  | fuel + 1, dom, groups, activeAddrs => do
  -- A helper family can occur at an unrelated specialization while it is on
  -- the nested traversal stack. Only expressions that still contain the
  -- original block are recursive occurrences for this positivity check.
  let some rootGroup := groups[0]?
    | throw (.other "positivity: missing root-family context")
  let rootAddrs := rootGroup.addrs
  if !exprMentionsAnyAddr dom rootAddrs then
    return ()
  let w ← whnf dom
  match w with
  | .all _ _ innerDom innerBody _ =>
    -- Inductive in the domain of a Pi = negative position.
    if exprMentionsAnyAddr innerDom rootAddrs then
      throw (.other "strict positivity violation")
    -- H4: open with an fvar so whnf works on dependent types.
    let saved := (← get).lctx.size
    let (innerOpen, _) ← TcM.openBinderAnon innerDom innerBody
    let result ←
      try
        checkPositivityDomainFuel fuel innerOpen groups activeAddrs
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
    modify fun s => { s with lctx := s.lctx.truncate saved }
    match result with
    | .ok () => return ()
    | .error e => throw e
  | _ =>
    let (head, args) := w.collectSpine
    match head with
    | .const id us _ =>
      if rootAddrs.contains id.addr then
        return (← checkPositiveRecursiveApplication id us args groups rootAddrs)
      -- Nested inductive: external inductive whose params mention the block.
      let (nParams, nIndices, lvls, block, ctors) ←
        match (← TcM.getConst id) with
        | .indc (params := params) (indices := indices) (lvls := lvls)
            (block := block) (ctors := ctors) .. =>
          pure (params.toNat, indices.toNat, lvls.toNat, block, ctors)
        | _ => throw (.other "positivity: not a valid inductive app")
      if args.size != nParams + nIndices || us.size != lvls then
        throw (.other "positivity: malformed nested inductive application")
      -- Repeated exact specialization closes an already-validated auxiliary
      -- edge. The same address at a different specialization is a new
      -- auxiliary, as in the two Array specializations of Lean.Doc.Block.
      for group in groups do
        if group.addrs.contains id.addr &&
            positivityGroupMatches group id.addr us args nParams then
          for index in args.extract nParams args.size do
            if exprMentionsAnyAddr index rootAddrs then
              throw (.other "positivity: recursive occurrence index mentions an active inductive")
          return ()
      let hasNestedRef := (args.extract 0 (min nParams args.size)).any
        (exprMentionsAnyAddr · rootAddrs)
      if !hasNestedRef then
        throw (.other "positivity: not a valid inductive app")
      -- Index args (after params) must not mention block inductives.
      for arg in args.extract nParams args.size do
        if exprMentionsAnyAddr arg rootAddrs then
          throw (.other "positivity: index mentions block inductive")
      -- Augmented address set: block + the external inductive's block.
      let extBlockInductives ← discoverBlockInductives block
      let extAddrs := extBlockInductives.map (·.addr)
      let augmented := activeAddrs ++ extAddrs
      let paramArgs := args.extract 0 (min nParams args.size)
      let augmentedGroups := groups.push
        { addrs := extAddrs, params := paramArgs, concreteUs := some us }
      for ctorId in ctors do
        let ctorTy ← match (← TcM.getConst ctorId) with
          | .ctor (ty := ty) .. => pure ty
          | _ => throw (.other "positivity: nested ctor not found")
        checkNestedCtorFieldsFuel fuel ctorTy nParams paramArgs us
          augmentedGroups augmented
    | _ => throw (.other "positivity: not a valid inductive app")

/-- Nested-inductive field positivity: instantiate universes, strip the
    external inductive's param binders, simultaneously substitute the
    actual (block-mentioning) parameter arguments, then check each
    remaining field domain against the augmented address set. -/
def checkNestedCtorFields (ctorTy : KExpr m) (nParams : Nat)
    (paramArgs : Array (KExpr m)) (us : Array (KUniv m))
    (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) : RecM m Unit :=
  checkNestedCtorFieldsFuel maxWhnfFuel.toNat ctorTy nParams paramArgs us
    groups activeAddrs

def checkNestedCtorFieldsFuel :
    Nat → KExpr m → Nat → Array (KExpr m) → Array (KUniv m) →
      Array (PositivityGroup m) → Array Address → RecM m Unit
  | 0, _, _, _, _, _, _ => throw .maxRecDepth
  | fuel + 1, ctorTy, nParams, paramArgs, us, groups, activeAddrs => do
  let mut ty ← TcM.instantiateUnivParams ctorTy us
  for _ in [0:nParams] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ => ty := body
    | _ => return ()
  -- Var(0) = innermost = LAST param after stripping; simulSubst maps
  -- Var(i) ↦ substs[i], so reverse the param order.
  ty ← TcM.runIntern (simulSubst ty paramArgs.reverse 0)
  checkNestedCtorFieldsLoopFuel fuel ty groups activeAddrs

def checkNestedCtorFieldsLoop (ty : KExpr m)
    (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) : RecM m Unit :=
  checkNestedCtorFieldsLoopFuel maxWhnfFuel.toNat ty groups activeAddrs

def checkNestedCtorFieldsLoopFuel :
    Nat → KExpr m → Array (PositivityGroup m) → Array Address → RecM m Unit
  | 0, _, _, _ => throw .maxRecDepth
  | fuel + 1, ty, groups, activeAddrs => do
  let w ← whnf ty
  match w with
  | .all _ _ dom body _ =>
    checkPositivityDomainFuel fuel dom groups activeAddrs
    let saved := (← get).lctx.size
    let (open', _) ← TcM.openBinderAnon dom body
    let result ←
      try
        checkNestedCtorFieldsLoopFuel fuel open' groups activeAddrs
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
    modify fun s => { s with lctx := s.lctx.truncate saved }
    match result with
    | .ok () => return ()
    | .error e => throw e
  | _ => return ()

/-- A4: field sort levels ≤ the inductive's result level (Prop inductives
    are exempt). -/
def checkFieldUniverses (ctorTy : KExpr m) (nParams : Nat)
    (indLevel : KUniv m) : RecM m Unit := do
  if indLevel.isSemanticZero then
    return ()
  let saved := (← get).lctx.size
  let mut ty := ctorTy
  for _ in [0:nParams] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let (open', _) ← TcM.openBinderAnon dom body
      ty := open'
    | _ => break
  let _ ← runBounded (fun ty => do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let domTy ← infer dom
      let fieldLevel ← ensureSortDirect domTy
      if !univGeq indLevel fieldLevel then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other "field universe exceeds inductive level")
      let (open', _) ← TcM.openBinderAnon dom body
      return .next open'
    | _ => return .done ()) maxWhnfFuel.toNat ty
  modify fun s => { s with lctx := s.lctx.truncate saved }

/-- A2: constructor return type (see module doc for the exact conditions). -/
def checkCtorReturnType (ctorTy : KExpr m)
    (nParams nIndices nFields : Nat) (indAddr : Address) (indLvls : UInt64)
    (blockAddrs : Array Address) : RecM m Unit := do
  let saved := (← get).lctx.size
  let mut ty := ctorTy
  let totalBinders := nParams + nFields
  let mut paramFVars : Array (KExpr m) := Array.mkEmpty nParams
  for i in [0:totalBinders] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let (open', fv, _) ← TcM.openBinderAnonWithFV dom body
      if i < nParams then
        paramFVars := paramFVars.push fv
      ty := open'
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: not enough binders")
  -- Do NOT whnf: the return type must be a *manifest* `I args…`.
  let (head, args) := ty.collectSpine
  match head with
  | .const id us _ =>
    if id.addr != indAddr then
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: head is not the inductive")
    if us.size.toUInt64 != indLvls then
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other s!"ctor return type: expected {indLvls} universe args, got {us.size}")
    for i in [0:us.size] do
      let expected : KUniv m := .mkParam i.toUInt64 anonN
      if !univEq us[i]! expected then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other s!"ctor return type: universe arg {i} is not Param({i})")
  | _ =>
    modify fun s => { s with lctx := s.lctx.truncate saved }
    throw (.other "ctor return type: head is not the inductive")
  -- S2: exact arg count.
  if args.size != nParams + nIndices then
    modify fun s => { s with lctx := s.lctx.truncate saved }
    throw (.other s!"ctor return type: expected {nParams + nIndices} args (params={nParams} + indices={nIndices}), got {args.size}")
  -- First nParams args are exactly the param fvars.
  for i in [0:nParams] do
    match args[i]? with
    | none =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: not enough args for params")
    | some arg =>
      if arg.addr != paramFVars[i]!.addr then
        modify fun s => { s with lctx := s.lctx.truncate saved }
        throw (.other "ctor return type: param arg not the param fvar")
  -- Index args must not mention block inductives.
  for arg in args.extract nParams args.size do
    if exprMentionsAnyAddr arg blockAddrs then
      modify fun s => { s with lctx := s.lctx.truncate saved }
      throw (.other "ctor return type: index mentions block inductive")
  modify fun s => { s with lctx := s.lctx.truncate saved }

-- ### Member / block validation

/-- Validate the constructor header fields which Lean derives from the parent
    inductive declaration. Ix consumes these fields operationally (`cidx` for
    iota dispatch, arities for applications/projections, and `isUnsafe` for
    the safety lattice), so a well-typed constructor telescope alone is not a
    sufficient admission check. -/
def checkCtorMetadataAgainstParent (ctorId inductId : KId m)
    (expectedCidx indParams : Nat) (indLvls : UInt64)
    (indIsUnsafe : Bool) : RecM m (KExpr m × Nat) := do
  let (ctorTy, ctorInduct, ctorCidx, ctorParams, ctorFields, ctorLvls,
      ctorIsUnsafe) ← match (← TcM.getConst ctorId) with
    | .ctor (ty := ty) (induct := induct) (cidx := cidx)
        (params := params) (fields := fields) (lvls := lvls)
        (isUnsafe := isUnsafe) .. =>
      pure (ty, induct, cidx.toNat, params.toNat, fields.toNat, lvls,
        isUnsafe)
    | _ => throw (.other "check_inductive: constructor not found")
  if ctorInduct != inductId then
    throw (.other "check_inductive: ctor parent mismatch")
  if ctorLvls != indLvls then
    throw (.other s!"check_inductive: ctor universe arity mismatch: expected {indLvls}, got {ctorLvls}")
  if ctorIsUnsafe != indIsUnsafe then
    throw (.other s!"check_inductive: ctor safety mismatch: expected {indIsUnsafe}, got {ctorIsUnsafe}")
  if ctorParams != indParams then
    throw (.other s!"check_inductive: ctor params mismatch: expected {indParams}, got {ctorParams}")
  if ctorCidx != expectedCidx then
    throw (.other s!"check_inductive: ctor cidx mismatch: expected {expectedCidx}, got {ctorCidx}")
  return (ctorTy, ctorFields)

/-- Validate an inductive and every one of its constructors (S3/S3b peer
    agreement + A1–A4). The Rust tail (recursor-generation trigger) lands
    with P9. -/
def checkInductiveMemberImpl (id : KId m) : RecM m Unit := do
  let (params, indices, lvls, ctors, block, isUnsafe, ty) ←
    match (← TcM.getConst id) with
    | .indc (params := params) (indices := indices) (lvls := lvls)
        (ctors := ctors) (block := block) (isUnsafe := isUnsafe)
        (ty := ty) .. =>
      pure (params, indices, lvls, ctors, block, isUnsafe, ty)
    | _ => throw (.other "check_inductive: not an inductive")
  let blockInds ← discoverBlockInductives block
  let blockAddrs := blockInds.map (·.addr)
  -- Result sort must exist even for ctor-less inductives.
  let indArity ← checkedMetadataSum "inductive params + indices"
    #[params, indices]
  let indLevel ← getResultSortLevel ty indArity.toNat
  -- S3/S3b, memoized per block (transitive agreement).
  if !(← get).env.blockPeerAgreementCache.contains block then
    for peerId in blockInds do
      if peerId.addr == id.addr then
        continue
      let (peerParams, peerIndices, peerLvls, peerIsUnsafe, peerTy) ←
        match (← TcM.getConst peerId) with
        | .indc (params := pp) (indices := pi) (lvls := pl)
            (isUnsafe := pu) (ty := pty) .. =>
          pure (pp, pi, pl, pu, pty)
        | _ => continue
      let peerArity ← checkedMetadataSum "inductive params + indices"
        #[peerParams, peerIndices]
      let peerLevel ← getResultSortLevel peerTy peerArity.toNat
      if !univEq indLevel peerLevel then
        throw (.other "mutually inductive types must live in the same universe")
      if peerLvls != lvls then
        throw (.other s!"mutual peers must declare the same universe arity: self={lvls}, peer={peerLvls}")
      if peerIsUnsafe != isUnsafe then
        throw (.other "mutual inductives must share the same safety flag")
      if peerParams != params then
        throw (.other s!"mutual peers must declare the same number of parameters: self={params}, peer={peerParams}")
      checkParamAgreement ty peerTy params.toNat
    modify fun s => { s with env := { s.env with
      blockPeerAgreementCache := s.env.blockPeerAgreementCache.insert block } }
  -- Per-constructor A1–A4.
  for h : expectedCidx in [0:ctors.size] do
    let ctorId := ctors[expectedCidx]
    let (ctorTy, ctorFields) ← checkCtorMetadataAgainstParent ctorId id
      expectedCidx params.toNat lvls isUnsafe
    checkParamAgreement ty ctorTy params.toNat
    if !isUnsafe then
      checkPositivity ctorTy params.toNat blockAddrs
    checkFieldUniverses ctorTy params.toNat indLevel
    checkCtorReturnType ctorTy params.toNat indices.toNat ctorFields
      id.addr lvls blockAddrs
  -- Recursor generation for the block (fatal — silent failure would let
  -- an unverifiable recursor slip through).
  if !(← get).env.recursorCache.contains block then
    generateBlockRecursors block

/-- Standalone-constructor validation: the same per-ctor A1–A4 against the
    declared parent. -/
def checkCtorAgainstInductiveMemberImpl (ctorId inductId : KId m) :
    RecM m Unit := do
  let (indParams, indIndices, indLvls, indBlock, indIsUnsafe, indTy,
      indCtors) ←
    match (← TcM.getConst inductId) with
    | .indc (params := params) (indices := indices) (lvls := lvls)
        (block := block) (isUnsafe := isUnsafe) (ty := ty)
        (ctors := ctors) .. =>
      pure (params, indices, lvls, block, isUnsafe, ty, ctors)
    | _ => throw (.other "check_ctor: parent inductive not found")
  let mut expectedCidx? : Option Nat := none
  for h : idx in [0:indCtors.size] do
    if indCtors[idx] == ctorId then
      if expectedCidx?.isSome then
        throw (.other "check_inductive: ctor listed more than once by parent")
      expectedCidx? := some idx
  let some expectedCidx := expectedCidx?
    | throw (.other "check_inductive: ctor not listed by parent")
  let (ctorTy, ctorFields) ← checkCtorMetadataAgainstParent ctorId inductId
    expectedCidx indParams.toNat indLvls indIsUnsafe
  let blockInds ← discoverBlockInductives indBlock
  let blockAddrs := blockInds.map (·.addr)
  let indArity ← checkedMetadataSum "inductive params + indices"
    #[indParams, indIndices]
  let indLevel ← getResultSortLevel indTy indArity.toNat
  checkParamAgreement indTy ctorTy indParams.toNat
  if !indIsUnsafe then
    checkPositivity ctorTy indParams.toNat blockAddrs
  checkFieldUniverses ctorTy indParams.toNat indLevel
  checkCtorReturnType ctorTy indParams.toNat indIndices.toNat ctorFields
    inductId.addr indLvls blockAddrs

/-- Validate every inductive and constructor of a homogeneous inductive
    block: per-member well-scopedness + type inference, then the member
    checks. -/
def checkInductiveBlockImpl (block : KId m) (members : Array (KId m)) :
    RecM m Unit := do
  let mut indIds : Array (KId m) := #[]
  let mut ctorIds : Array (KId m) := #[]
  -- SECURITY INVARIANT (Lean #14576): infer each original stored member
  -- type, including every constructor type, before building or consulting
  -- any flattened/nested-inductive representation. A lossy nested rewrite
  -- can erase phantom parameter arguments; checking only that rewritten
  -- form would let an ill-typed argument disappear. Keep this pass in full
  -- inference mode and over the untouched `ty` values.
  for member in members do
    TcM.reset (m := m)
    let c ← TcM.getConst member
    validateConstWellScoped c
    match c with
    | .indc (ty := ty) .. =>
      let t ← infer ty
      let _ ← ensureSortDirect t
      indIds := indIds.push member
    | .ctor (ty := ty) .. =>
      let t ← infer ty
      let _ ← ensureSortDirect t
      ctorIds := ctorIds.push member
    | _ =>
      throw (.other s!"check_inductive_block: non-inductive member {member} in block {block}")
  for indId in indIds do
    TcM.reset (m := m)
    checkInductiveMemberImpl indId
  for ctorId in ctorIds do
    let induct ← match (← TcM.getConst ctorId) with
      | .ctor (induct := induct) .. => pure induct
      | _ => continue
    TcM.reset (m := m)
    checkCtorAgainstInductiveMemberImpl ctorId induct

-- ### Recursor generation

/-- Shifted universe param args: `[param offset, …, param (lvls-1+offset)]`
    (offset 1 for large eliminators). -/
def mkIndUnivs (indLvls offset : UInt64) :
    RecM m (Array (KUniv m)) := do
  let _ ← checkedMetadataSum "generated recursor universe arity"
    #[indLvls, offset]
  let mut out : Array (KUniv m) := Array.mkEmpty indLvls.toNat
  for i in [0:indLvls.toNat] do
    out := out.push (← TcM.internUniv (m := m) (.mkParam (i.toUInt64 + offset) anonN))
  return out

/-- Core of nested-occurrence detection (early-return style; the caller
    restores the lctx). Structural forall peel — NO whnf (a defn head like
    `IO.Ref` is not a nested occurrence). -/
def tryDetectNestedCore (dom : KExpr m) (blockAddrs : Array Address)
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64)
    (paramDepth : Nat) (nRecParams : UInt64) :
    RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey) := do
  let cur ← runBounded (fun cur => do
    match cur with
    | .all _ _ innerDom body _ =>
      let (open', _) ← TcM.openBinderAnon innerDom body
      return .next open'
    | _ => return .done cur) maxWhnfFuel.toNat dom
  let (head, args) := cur.collectSpine
  let some headId := (match head with
      | .const id _ _ => some id
      | _ => none)
    | return (flat, auxSeen)
  -- Direct recursion (block member) or already-detected original.
  if blockAddrs.contains headId.addr then
    return (flat, auxSeen)
  if flat.any (fun mem => mem.id.addr == headId.addr && !mem.isAux) then
    return (flat, auxSeen)
  let (extParams, extIndices, extCtors, extLvls) ←
    match (← TcM.tryGetConst headId) with
    | some (.indc (params := extParams) (indices := extIndices)
        (ctors := extCtors) (lvls := extLvls) ..) =>
      pure (extParams, extIndices, extCtors, extLvls)
    | _ => return (flat, auxSeen)
  let extNParams := extParams.toNat
  if args.size < extNParams then
    return (flat, auxSeen)
  -- Some param arg must mention a block ORIGINAL (aux flat addrs would
  -- falsely match unrelated occurrences).
  let hasNestedRef := (args.extract 0 extNParams).any
    (exprMentionsAnyAddr · blockAddrs)
  if !hasNestedRef then
    return (flat, auxSeen)
  let specParams := args.extract 0 extNParams
  -- S7: reject param args depending on field/domain-local binders.
  let paramBound ← checkedNatMetadataSum "nested parameter scope"
    #[paramDepth, nRecParams.toNat]
  let s7ok := specParams.all fun sp =>
    !sp.hasFVars && sp.lbr ≤ paramBound
  if !s7ok then
    return (flat, auxSeen)
  let occurrenceUs := match head with
    | .const _ us _ => us
    | _ => #[]
  let specialization := NestedSpecializationKey.ofApplication headId.addr
    occurrenceUs specParams
  if auxSeen.contains specialization then
    return (flat, auxSeen)
  let auxSeen' := auxSeen.push specialization
  let auxUs ← mkIndUnivs extLvls univOffset
  let flat' := flat.push
    { id := headId, isAux := true, specParams,
      ownParams := extParams, nIndices := extIndices,
      ctors := extCtors, lvls := extLvls, indUs := auxUs, occurrenceUs }
  return (flat', auxSeen')

/-- Detect whether `dom` is a nested inductive occurrence; if so append an
    auxiliary entry (dedup by family, universe, and parameter addresses).
    Returns the updated `(flat, auxSeen)`; lctx restored. -/
def tryDetectNested (dom : KExpr m) (blockAddrs : Array Address)
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64)
    (paramDepth : Nat) (nRecParams : UInt64) :
    RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey) := do
  let savedLctx := (← get).lctx.size
  let result ← tryDetectNestedCore dom blockAddrs flat auxSeen univOffset
    paramDepth nRecParams
  modify fun s => { s with lctx := s.lctx.truncate savedLctx }
  return result

/-- Build the flat block: originals seeded, then a queue pass over every
    member's ctor fields detecting nested occurrences. -/
def buildFlatBlock (blockInds : Array (KId m))
    (nRecParams univOffset : UInt64) :
    RecM m (Array (FlatBlockMember m)) := do
  let allBlockAddrs := blockInds.map (·.addr)
  let mut flat : Array (FlatBlockMember m) := #[]
  let mut auxSeen : Array NestedSpecializationKey := #[]
  for indId in blockInds do
    match (← TcM.getConst indId) with
    | .indc (params := ownParams) (indices := nIndices) (ctors := ctors)
        (lvls := lvls) .. =>
      let indUs ← mkIndUnivs lvls univOffset
      let mut specParams : Array (KExpr m) := Array.mkEmpty nRecParams.toNat
      for j in [0:nRecParams.toNat] do
        specParams := specParams.push
          (.mkVar (nRecParams - 1 - j.toUInt64) anonN)
      flat := flat.push
        { id := indId, isAux := false, specParams, ownParams, nIndices,
          ctors, lvls, indUs, occurrenceUs := indUs }
    | _ => continue
  -- Queue-based scan (flat grows while iterating).
  runBounded (fun (qi, flat0, auxSeen0) => do
    if qi ≥ flat0.size then
      return .done flat0
    let member := flat0[qi]!
    let mut flat := flat0
    let mut auxSeen := auxSeen0
    for ctorId in member.ctors do
      let (ctorFields, ctorTy) ← match (← TcM.tryGetConst ctorId) with
        | some (.ctor (fields := fields) (ty := ty) ..) => pure (fields, ty)
        | _ => continue
      let ctorTyInst ← TcM.instantiateUnivParams ctorTy member.occurrenceUs
      let saved := (← get).lctx.size
      let mut cur := ctorTyInst
      for j in [0:member.ownParams.toNat] do
        let w ← whnf cur
        match w with
        | .all _ _ _ body _ =>
          let p := if j < member.specParams.size then
              member.specParams[j]!
            else
              .mkVar (nRecParams - 1 - j.toUInt64) anonN
          cur ← TcM.runIntern (subst body p 0)
        | _ => break
      for _ in [0:ctorFields.toNat] do
        let w ← whnf cur
        match w with
        | .all _ _ dom body _ =>
          let (flat', auxSeen') ← tryDetectNested dom allBlockAddrs flat
            auxSeen univOffset saved nRecParams
          flat := flat'
          auxSeen := auxSeen'
          let (open', _) ← TcM.openBinderAnon dom body
          cur := open'
        | _ => break
      modify fun s => { s with lctx := s.lctx.truncate saved }
    return .next (qi + 1, flat, auxSeen)) maxWhnfFuel.toNat
      (0, flat, auxSeen)

/-- Rewrite one nested occurrence `Ext spec idx…` to
    `aux blockParams idx…` when the head+params match an aux member. -/
def tryReplaceAuxRefForSort (e : KExpr m)
    (aux : Array (FlatBlockMember m)) (auxIds : Array (KId m))
    (blockUs : Array (KUniv m)) (nBlockParams localDepth : UInt64) :
    RecM m (Option (KExpr m)) := do
  let (head, args) := e.collectSpine
  let some headId := (match head with
      | .const id _ _ => some id
      | _ => none)
    | return none
  for h : idx in [0:aux.size] do
    let member := aux[idx]
    if member.id.addr != headId.addr then
      continue
    let own := member.ownParams.toNat
    if args.size < own || member.specParams.size != own then
      continue
    let mut matched := true
    for i in [0:own] do
      let spLifted ← if localDepth > 0 then
          TcM.runIntern (lift member.specParams[i]! localDepth 0)
        else
          pure member.specParams[i]!
      let ok ← try isDefEq args[i]! spLifted catch _ => pure false
      if !ok then
        matched := false
        break
    if !matched then
      continue
    let mut result ← TcM.intern (.mkConst auxIds[idx]! blockUs)
    let paramBase ← checkedMetadataSum "auxiliary parameter index"
      #[localDepth, nBlockParams]
    for pi in [0:nBlockParams.toNat] do
      let p ← TcM.intern (m := m)
        (.mkVar (paramBase - 1 - pi.toUInt64) anonN)
      result ← TcM.intern (.mkApp result p)
    for idxArg in args.extract own args.size do
      result ← TcM.intern (.mkApp result idxArg)
    return some result
  return none

/-- Rewrite ALL nested occurrences in `e` to block-local synthetic aux
    references (pre-sort normalization; compile-side `replace_all_nested`). -/
def replaceAuxRefsForSort (e : KExpr m)
    (aux : Array (FlatBlockMember m)) (auxIds : Array (KId m))
    (blockUs : Array (KUniv m)) (nBlockParams localDepth : UInt64) :
    RecM m (KExpr m) := do
  if let some replaced ← tryReplaceAuxRefForSort e aux auxIds blockUs
      nBlockParams localDepth then
    return replaced
  match e with
  | .app f a _ =>
    let f2 ← replaceAuxRefsForSort f aux auxIds blockUs nBlockParams localDepth
    let a2 ← replaceAuxRefsForSort a aux auxIds blockUs nBlockParams localDepth
    TcM.intern (.mkApp f2 a2)
  | .lam n bi ty body _ =>
    let ty2 ← replaceAuxRefsForSort ty aux auxIds blockUs nBlockParams localDepth
    let body2 ← replaceAuxRefsForSort body aux auxIds blockUs nBlockParams
      (localDepth + 1)
    TcM.intern (.mkLam n bi ty2 body2)
  | .all n bi ty body _ =>
    let ty2 ← replaceAuxRefsForSort ty aux auxIds blockUs nBlockParams localDepth
    let body2 ← replaceAuxRefsForSort body aux auxIds blockUs nBlockParams
      (localDepth + 1)
    TcM.intern (.mkAll n bi ty2 body2)
  | .letE n ty val body nd _ =>
    let ty2 ← replaceAuxRefsForSort ty aux auxIds blockUs nBlockParams localDepth
    let val2 ← replaceAuxRefsForSort val aux auxIds blockUs nBlockParams localDepth
    let body2 ← replaceAuxRefsForSort body aux auxIds blockUs nBlockParams
      (localDepth + 1)
    TcM.intern (.mkLet n ty2 val2 body2 nd)
  | .prj id field val _ =>
    let val2 ← replaceAuxRefsForSort val aux auxIds blockUs nBlockParams localDepth
    TcM.intern (.mkPrj id field val2)
  | _ => return e

/-- First `n` Pi binders of the block's first inductive, outermost-first
    (domains stay in the recursor-external telescope context). -/
def extractBlockParamBinders (blockFirstId : KId m)
    (nBlockParams : UInt64) :
    RecM m (Array (m.F Name × m.F Lean.BinderInfo × KExpr m)) := do
  let indTy ← match (← TcM.tryGetConst blockFirstId) with
    | some (.indc (ty := ty) ..) => pure ty
    | _ => return #[]
  let mut out : Array (m.F Name × m.F Lean.BinderInfo × KExpr m) :=
    Array.mkEmpty nBlockParams.toNat
  let mut cur := indTy
  for _ in [0:nBlockParams.toNat] do
    let w ← whnf cur
    match w with
    | .all name bi dom body _ =>
      out := out.push (name, bi, dom)
      cur := body
    | _ => break
  return out

/-- `∀ T₀ … Tₙ₋₁, body` from outermost-first binders (compile-side
    `mk_forall`). -/
def wrapWithBlockParamForalls (body : KExpr m)
    (binders : Array (m.F Name × m.F Lean.BinderInfo × KExpr m)) :
    RecM m (KExpr m) := do
  let mut cur := body
  for i in [0:binders.size] do
    let (name, bi, dom) := binders[binders.size - 1 - i]!
    cur ← TcM.intern (.mkAll name bi dom cur)
  return cur

/-- Kernel analogue of the compile-side aux partition-refinement sort:
    synthesize `Indc`/`Ctor` views for each aux (spec-param instantiated,
    aux-ref rewritten, block-param wrapped), seed by compiler-shaped name
    rank, run `sortKConstsWithSeedKey`, and return
    `perm[k] = original index of class k's representative`. -/
def canonicalAuxOrder (aux : Array (FlatBlockMember m))
    (nBlockParams : UInt64) (blockUs : Array (KUniv m))
    (all0Name : Option Name) (blockFirstId : Option (KId m)) :
    RecM m (Array Nat) := do
  let nestedPrefix := all0Name.map (Ix.Name.mkStr · "_nested")
  let blockParamBinders ← match blockFirstId with
    | some id =>
      if nBlockParams > 0 then extractBlockParamBinders id nBlockParams
      else pure #[]
    | none => pure #[]
  -- Synthetic aux ids + compiler-shaped seed names.
  let mut auxIds : Array (KId m) := Array.mkEmpty aux.size
  let mut auxSeedNames : Array Name := Array.mkEmpty aux.size
  for h : sourceIdx in [0:aux.size] do
    let member := aux[sourceIdx]
    -- `Name.pretty` (bare, un-escaped), NOT `toString`: Rust seeds on
    -- `name.pretty()`, and the seed string feeds the canonical sort.
    let extSeed := match Mode.get? member.id.name with
      | some name => name.pretty.replace "." "_"
      | none => toString member.id.addr
    let seedSuffix := s!"{extSeed}_{sourceIdx + 1}"
    let seedName := match nestedPrefix with
      | some prefix' => prefix'.mkStr seedSuffix
      | none => (Ix.Name.mkAnon.mkStr "IxKernelAux").mkStr seedSuffix
    let mut h := Blake3.Rust.Hasher.init ()
    h := h.update "AUX_INDC_VIEW".toUTF8
    h := h.update sourceIdx.toUInt64.toLEBytes
    h := h.update member.id.addr.hash
    for sp in member.specParams do
      h := h.update sp.addr.hash
    for u in member.occurrenceUs do
      h := h.update u.addr.hash
    let auxAddr := Address.mk (h.finalizeWithLength 32).val
    auxIds := auxIds.push ⟨auxAddr, Mode.field seedName⟩
    auxSeedNames := auxSeedNames.push seedName
  -- Monotone seed ranks in sorted-name order (Name Ord = hash bytes).
  let mut seedOrder := (Array.range auxSeedNames.size)
  seedOrder := seedOrder.qsort fun a b =>
    Address.cmpBytes auxSeedNames[a]!.getHash auxSeedNames[b]!.getHash == .lt
  let mut seedKeyByAddr : Std.HashMap Address Address := {}
  for h : rank in [0:seedOrder.size] do
    let sourceIdx := seedOrder[rank]
    let rank64 := rank.toUInt64
    let mut bytes : ByteArray := .empty
    for i in [0:8] do
      bytes := bytes.push (rank64 >>> ((7 - i.toUInt64) * 8)).toUInt8
    for _ in [0:24] do
      bytes := bytes.push 0
    seedKeyByAddr := seedKeyByAddr.insert auxIds[sourceIdx]!.addr
      (Address.mk bytes)
  -- Synthetic Indc + Ctor views.
  let mut auxIndcs : Array (KId m × KConst m) := Array.mkEmpty aux.size
  let mut allCtorLookup : Std.HashMap Address (KConst m) := {}
  let syntheticBlock : KId m :=
    ⟨Address.blake3 "synthetic-aux-block".toUTF8, Mode.field .mkAnon⟩
  for h : sourceIdx in [0:aux.size] do
    let member := aux[sourceIdx]
    let auxId := auxIds[sourceIdx]!
    let seedName := auxSeedNames[sourceIdx]!
    let (extTy, extCtors, extNParams, extNIndices) ←
      match (← TcM.getConst member.id) with
      | .indc (ty := ty) (ctors := ctors) (params := params)
          (indices := indices) .. => pure (ty, ctors, params, indices)
      | _ => throw (.other "canonical_aux_order: aux ext is not an inductive")
    let mut typ ← TcM.instantiateUnivParams extTy member.occurrenceUs
    for j in [0:extNParams.toNat] do
      let w ← whnf typ
      match w with
      | .all _ _ _ body _ =>
        if j ≥ member.specParams.size then
          break
        typ ← TcM.runIntern (subst body member.specParams[j]! 0)
      | _ => break
    typ ← replaceAuxRefsForSort typ aux auxIds blockUs nBlockParams 0
    typ ← wrapWithBlockParamForalls typ blockParamBinders
    let mut auxCtorKids : Array (KId m) := Array.mkEmpty extCtors.size
    for hc : ci in [0:extCtors.size] do
      let extCtorId := extCtors[ci]
      let (extCtorTy, extCtorFields) ← match (← TcM.getConst extCtorId) with
        | .ctor (ty := ty) (fields := fields) .. => pure (ty, fields)
        | _ => throw (.other "canonical_aux_order: aux ext ctor is not a ctor")
      let mut ctorTyp ← TcM.instantiateUnivParams extCtorTy member.occurrenceUs
      for j in [0:extNParams.toNat] do
        let w ← whnf ctorTyp
        match w with
        | .all _ _ _ body _ =>
          if j ≥ member.specParams.size then
            break
          ctorTyp ← TcM.runIntern (subst body member.specParams[j]! 0)
        | _ => break
      ctorTyp ← replaceAuxRefsForSort ctorTyp aux auxIds blockUs nBlockParams 0
      ctorTyp ← wrapWithBlockParamForalls ctorTyp blockParamBinders
      let mut ch := Blake3.Rust.Hasher.init ()
      ch := ch.update "AUX_CTOR_VIEW".toUTF8
      ch := ch.update auxId.addr.hash
      ch := ch.update extCtorId.addr.hash
      let auxCtorAddr := Address.mk (ch.finalizeWithLength 32).val
      let auxCtorKid : KId m := ⟨auxCtorAddr, Mode.field .mkAnon⟩
      let auxCtor : KConst m := .ctor (Mode.field .mkAnon) Mode.F.mkDefault
        false blockUs.size.toUInt64 auxId ci.toUInt64 nBlockParams
        extCtorFields ctorTyp
      allCtorLookup := allCtorLookup.insert auxCtorAddr auxCtor
      auxCtorKids := auxCtorKids.push auxCtorKid
    -- Synthetic trailing "identity marker" ctor carrying the aux's
    -- nested-occurrence identity (`Ext spec_params`, pre-rewrite: NOT
    -- passed through `replaceAuxRefsForSort`, or it would become the
    -- self-reference and lose the distinction). Two nested occurrences
    -- of one external inductive can instantiate to alpha-identical
    -- views when the distinguishing spec param is phantom in the
    -- external's constructors — the marker keeps them in distinct
    -- classes and orders them by spec-param content, mirroring the
    -- compile-side marker in `sort_aux_by_partition_refinement` and the
    -- Rust kernel's `canonical_aux_order`. Omitting it mis-orders (or
    -- collapses) the aux classes of e.g. `Lean.Json` / `Lean.Doc.Block`
    -- / `Lean.Elab.InfoTree`, failing block recursor validation.
    let mut markerTy ← TcM.intern (m := m) (.mkConst member.id member.occurrenceUs)
    for sp in member.specParams do
      markerTy ← TcM.intern (KExpr.mkApp markerTy sp)
    let mut mh := Blake3.Rust.Hasher.init ()
    mh := mh.update "AUX_MARKER_VIEW".toUTF8
    mh := mh.update auxId.addr.hash
    let markerAddr := Address.mk (mh.finalizeWithLength 32).val
    let markerKid : KId m := ⟨markerAddr, Mode.field .mkAnon⟩
    let markerCtor : KConst m := .ctor (Mode.field .mkAnon) Mode.F.mkDefault
      false blockUs.size.toUInt64 auxId auxCtorKids.size.toUInt64 nBlockParams
      0 markerTy
    allCtorLookup := allCtorLookup.insert markerAddr markerCtor
    auxCtorKids := auxCtorKids.push markerKid
    let auxIndc : KConst m := .indc (Mode.field seedName) Mode.F.mkDefault
      blockUs.size.toUInt64 nBlockParams extNIndices false syntheticBlock 0
      typ auxCtorKids Mode.F.mkDefault
    auxIndcs := auxIndcs.push (auxId, auxIndc)
  -- Sort with the compiler-shaped seed key.
  let ctorLookup := allCtorLookup
  let seedKeys := seedKeyByAddr
  let classes ← TcM.ofExcept (sortKConstsWithSeedKey
    (fun cid => ctorLookup[cid.addr]?)
    (fun id _ => seedKeys[id.addr]?.getD id.addr)
    auxIndcs)
  -- Class representative → original index.
  let mut auxAddrToOrigIdx : Std.HashMap Address Nat := {}
  for h : i in [0:auxIndcs.size] do
    auxAddrToOrigIdx := auxAddrToOrigIdx.insert auxIndcs[i].1.addr i
  let mut perm : Array Nat := Array.mkEmpty classes.size
  for cls in classes do
    let some rep := cls[0]?
      | throw (.other "canonical_aux_order: empty class")
    let some origIdx := auxAddrToOrigIdx[rep.1.addr]?
      | throw (.other "canonical_aux_order: synthetic addr not in original index map")
    perm := perm.push origIdx
  return perm

/-- Motive type for a flat member:
    `∀ indices (t : I spec/params indices), Sort elim`. Built at depth 0. -/
def buildMotiveTypeFlat (member : FlatBlockMember m)
    (nRecParams : Nat) (elimLevel : KUniv m) : RecM m (KExpr m) := do
  let indTy := (← TcM.getConst member.id).ty
  let indTyInst ← TcM.instantiateUnivParams indTy member.occurrenceUs
  -- Peel own_params (subst spec_params / recursor-param Var refs).
  let mut ty := indTyInst
  for j in [0:member.ownParams.toNat] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ =>
      let p := if j < member.specParams.size then
          member.specParams[j]!
        else
          .mkVar (nRecParams.toUInt64 - 1 - j.toUInt64) anonN
      ty ← TcM.runIntern (subst body p 0)
    | _ => break
  -- Collect index domains.
  let mut indexDoms : Array (KExpr m) := #[]
  for _ in [0:member.nIndices.toNat] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      indexDoms := indexDoms.push dom
      ty := body
    | _ => break
  let nIdx := member.nIndices.toNat
  -- Major type at depth = nIdx.
  let mut majorTy ← TcM.intern (.mkConst member.id member.occurrenceUs)
  let depth ← checkedNatMetadataSum "generated motive index depth" #[nIdx]
  if !member.isAux then
    let paramBase ← checkedNatMetadataSum "generated motive parameter depth"
      #[nRecParams, nIdx]
    for i in [0:nRecParams] do
      let v ← TcM.intern (m := m)
        (.mkVar (paramBase - 1 - i.toUInt64) anonN)
      majorTy ← TcM.intern (.mkApp majorTy v)
  else
    for sp in member.specParams do
      let lifted ← if depth > 0 then TcM.runIntern (lift sp depth 0)
        else pure sp
      majorTy ← TcM.intern (.mkApp majorTy lifted)
  for i in [0:nIdx] do
    let v ← TcM.intern (m := m) (.mkVar (nIdx - 1 - i).toUInt64 anonN)
    majorTy ← TcM.intern (.mkApp majorTy v)
  -- ∀ (major : majorTy), Sort elim, wrapped in index foralls.
  let sort ← TcM.intern (.mkSort elimLevel)
  let mut result ← TcM.intern (.mkAll anonN anonBi majorTy sort)
  for i in [0:nIdx] do
    result ← TcM.intern (.mkAll anonN anonBi indexDoms[nIdx - 1 - i]! result)
  return result

/-- Recursive-field detection: after peeling foralls, `I_k params args`
    matching a flat member. Aux members additionally def-eq the first
    `ownParams` args against spec_params lifted by `specParamsLiftBy`. -/
def isRecField (dom : KExpr m) (flat : Array (FlatBlockMember m))
    (specParamsLiftBy : UInt64) : RecM m (Option Nat) := do
  runBounded (fun ty => do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ => return .next body
    | _ =>
      let (head, args) := w.collectSpine
      let some headAddr := (match head with
          | .const id _ _ => some id.addr
          | _ => none)
        | return .done none
      for h : idx in [0:flat.size] do
        let mem := flat[idx]
        if mem.id.addr != headAddr then
          continue
        if !mem.isAux then
          return .done (some idx)
        let own := mem.ownParams.toNat
        if args.size < own || mem.specParams.size != own then
          continue
        let mut allMatch := true
        for i in [0:own] do
          let spLifted ← if specParamsLiftBy > 0 then
              TcM.runIntern (lift mem.specParams[i]! specParamsLiftBy 0)
            else
              pure mem.specParams[i]!
          let ok ← try isDefEq args[i]! spLifted catch _ => pure false
          if !ok then
            allMatch := false
            break
        if allMatch then
          return .done (some idx)
      return .done none) maxWhnfFuel.toNat dom

/-- IH type for a recursive field (direct or forall-wrapped), built while
    fields and k earlier IHs are on the context. -/
def buildDirectIh (fieldIdx blockIndIdx nParams nFields k
    minorSaved motiveBase : Nat) (fieldDomains : Array (KExpr m))
    (blockAddrs : Array Address) : RecM m (KExpr m) := do
  -- Lift field domain from its depth (minorSaved + fieldIdx) to current
  -- (minorSaved + nFields + k).
  let dom := fieldDomains[fieldIdx]!
  let shift := (nFields + k - fieldIdx).toUInt64
  let domLifted ← TcM.runIntern (lift dom shift 0)
  let wdom ← whnf domLifted
  match wdom with
  | .all .. =>
    -- Forall-wrapped: ∀ xs…, I_bi params idxArgs(xs)
    let ihSaved := (← get).lctx.size
    let (forallDoms, innerWhnf) ← runBounded (fun (innerTy, forallDoms) => do
      let w ← whnf innerTy
      match w with
      | .all _ _ innerDom innerBody _ =>
        let (h, _) := w.collectSpine
        let isBlockHead := match h with
          | .const id _ _ => blockAddrs.contains id.addr
          | _ => false
        if isBlockHead then
          return .done (forallDoms, w)
        let _ ← TcM.pushFVarDeclAnon innerDom
        return .next (innerBody, forallDoms.push innerDom)
      | _ => return .done (forallDoms, w)) maxWhnfFuel.toNat (wdom, #[])
    let nXs := forallDoms.size
    let (_, innerArgs) := innerWhnf.collectSpine
    let idxArgs := innerArgs.extract nParams innerArgs.size
    let depth := (← TcM.depth (m := m)).toNat
    let motiveVar := (depth - 1 - (motiveBase + blockIndIdx)).toUInt64
    let mut ihBody : KExpr m := .mkVar motiveVar anonN
    for idx in idxArgs do
      ihBody ← TcM.intern (.mkApp ihBody idx)
    let fieldVar := (depth - 1 - (minorSaved + fieldIdx)).toUInt64
    let mut fieldApp : KExpr m := .mkVar fieldVar anonN
    for i in [0:nXs] do
      fieldApp ← TcM.intern (.mkApp fieldApp (.mkVar (nXs - 1 - i).toUInt64 anonN))
    ihBody ← TcM.intern (.mkApp ihBody fieldApp)
    for i in [0:nXs] do
      modify fun s => { s with lctx := s.lctx.truncate (s.lctx.size - 1) }
      ihBody := .mkAll anonN anonBi forallDoms[nXs - 1 - i]! ihBody
    modify fun s => { s with lctx := s.lctx.truncate ihSaved }
    return ihBody
  | _ =>
    let (_, domArgs) := wdom.collectSpine
    let idxArgs := domArgs.extract nParams domArgs.size
    let depth := (← TcM.depth (m := m)).toNat
    let motiveVar := (depth - 1 - (motiveBase + blockIndIdx)).toUInt64
    let mut ihBody : KExpr m := .mkVar motiveVar anonN
    for idx in idxArgs do
      ihBody ← TcM.intern (.mkApp ihBody idx)
    let fieldVar := (depth - 1 - (minorSaved + fieldIdx)).toUInt64
    ihBody ← TcM.intern (.mkApp ihBody (.mkVar fieldVar anonN))
    return ihBody

/-- Minor premise type for a constructor, built with params+motives on the
    context: `∀ fields ihs, motive(retIndices, C params fields)`. -/
def buildMinorAtDepth (indIdx : Nat) (ctorId : KId m)
    (member : FlatBlockMember m) (nRecParams motiveBase : Nat)
    (flat : Array (FlatBlockMember m)) (blockAddrs : Array Address) :
    RecM m (KExpr m) := do
  let ctorTyRaw ← match (← TcM.getConst ctorId) with
    | .ctor (ty := ty) .. => pure ty
    | _ => throw (.other "build_minor_at_depth: ctor not found")
  let saved := (← get).lctx.size
  let ctorTy ← TcM.instantiateUnivParams ctorTyRaw member.occurrenceUs
  -- Peel own_params.
  let mut ty := ctorTy
  for j in [0:member.ownParams.toNat] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ =>
      let p ← if !member.isAux then
          let depth ← TcM.depth (m := m)
          pure (KExpr.mkVar (depth - 1 - j.toUInt64) anonN)
        else if j < member.specParams.size then
          let sp := member.specParams[j]!
          let depth := (← TcM.depth (m := m)).toNat
          let liftBy := depth - min depth nRecParams
          if liftBy > 0 then TcM.runIntern (lift sp liftBy.toUInt64 0)
          else pure sp
        else
          let depth ← TcM.depth (m := m)
          pure (KExpr.mkVar (depth - 1 - j.toUInt64) anonN)
      ty ← TcM.runIntern (subst body p 0)
    | _ => break
  -- Collect fields (pushed as locals) + recursive-field positions.
  let (fieldsTy, fieldDomains, recFieldIndices, _) ← runBounded
      (fun (ty, fieldDomains, recFieldIndices, fidx) => do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let fieldDomains := fieldDomains.push dom
      let nRecParams64 := (flat[0]?.map (·.ownParams)).getD 0
      let liftBy := (← TcM.depth (m := m)) - min (← TcM.depth (m := m)) nRecParams64
      let mut recFieldIndices := recFieldIndices
      if let some bi ← isRecField dom flat liftBy then
        recFieldIndices := recFieldIndices.push (fidx, bi)
      let _ ← TcM.pushFVarDeclAnon dom
      return .next (body, fieldDomains, recFieldIndices, fidx + 1)
    | _ => return .done (ty, fieldDomains, recFieldIndices, fidx))
      maxWhnfFuel.toNat (ty, #[], #[], 0)
  let nFields := fieldDomains.size
  -- IH types (pushed as locals).
  let mut ihDomains : Array (KExpr m) := #[]
  for h : k in [0:recFieldIndices.size] do
    let (fieldIdx, blockIndIdx) := recFieldIndices[k]
    let targetNParams := if hlt : blockIndIdx < flat.size then
        flat[blockIndIdx].ownParams.toNat
      else nRecParams
    let ihTy ← buildDirectIh fieldIdx blockIndIdx targetNParams nFields k
      saved motiveBase fieldDomains blockAddrs
    ihDomains := ihDomains.push ihTy
    let _ ← TcM.pushFVarDeclAnon ihTy
  let nIhs := ihDomains.size
  let nBinders := nFields + nIhs
  -- Return type: I params indices → conclusion.
  let (_, retArgs) := fieldsTy.collectSpine
  let retIndices := retArgs.extract member.ownParams.toNat retArgs.size
  let depth := (← TcM.depth (m := m)).toNat
  let motiveVarIdx := (depth - 1 - (motiveBase + indIdx)).toUInt64
  let mut conclusion ← TcM.intern (m := m) (.mkVar motiveVarIdx anonN)
  for idxExpr in retIndices do
    let lifted ← if nIhs > 0 then TcM.runIntern (lift idxExpr nIhs.toUInt64 0)
      else pure idxExpr
    conclusion ← TcM.intern (.mkApp conclusion lifted)
  -- C params/spec fields.
  let mut ctorApp ← TcM.intern (.mkConst ctorId member.occurrenceUs)
  if !member.isAux then
    for i in [0:member.ownParams.toNat] do
      let pvar ← TcM.intern (m := m) (.mkVar (depth - 1 - i).toUInt64 anonN)
      ctorApp ← TcM.intern (.mkApp ctorApp pvar)
  else
    let liftBy := depth - min depth nRecParams
    for sp in member.specParams do
      let lifted ← if liftBy > 0 then TcM.runIntern (lift sp liftBy.toUInt64 0)
        else pure sp
      ctorApp ← TcM.intern (.mkApp ctorApp lifted)
  for i in [0:nFields] do
    let fvar ← TcM.intern (m := m) (.mkVar (nBinders - 1 - i).toUInt64 anonN)
    ctorApp ← TcM.intern (.mkApp ctorApp fvar)
  conclusion ← TcM.intern (.mkApp conclusion ctorApp)
  -- Fold ∀ ihs, then ∀ fields (inside-out; pop locals).
  for i in [0:nIhs] do
    modify fun s => { s with lctx := s.lctx.truncate (s.lctx.size - 1) }
    conclusion ← TcM.intern
      (.mkAll anonN anonBi ihDomains[nIhs - 1 - i]! conclusion)
  for i in [0:nFields] do
    modify fun s => { s with lctx := s.lctx.truncate (s.lctx.size - 1) }
    conclusion ← TcM.intern
      (.mkAll anonN anonBi fieldDomains[nFields - 1 - i]! conclusion)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  return conclusion

/-- Full recursor type for flat member `di`:
    `∀ params motives minors indices major, motive indices major`. -/
def buildRecType (di : Nat)
    (indInfos : Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m)) (univOffset : UInt64) :
    RecM m (KExpr m) := do
  let saved := (← get).lctx.size
  let nParams := indInfos[0]!.2.1.toNat
  let nMotives := indInfos.size
  let nIndices := indInfos[di]!.2.2.1.toNat
  let blockAddrs := blockInds.map (·.addr)
  let mut domains : Array (KExpr m) := #[]
  -- Params from the first inductive's type (shifted universes).
  let firstIndLvls ← match (← TcM.tryGetConst blockInds[0]!) with
    | some (.indc (lvls := lvls) ..) => pure lvls
    | _ => pure 0
  let firstIndUnivs ← mkIndUnivs firstIndLvls univOffset
  let mut pty ← TcM.instantiateUnivParams indInfos[0]!.2.2.2.2 firstIndUnivs
  for _ in [0:nParams] do
    let w ← whnf pty
    match w with
    | .all _ _ dom body _ =>
      domains := domains.push dom
      let _ ← TcM.pushFVarDeclAnon dom
      pty := body
    | _ => break
  -- Motives (motive j lifted by j).
  for h : j in [0:motiveTypes.size] do
    let mt := motiveTypes[j]
    let liftedMt ← if j > 0 then TcM.runIntern (lift mt j.toUInt64 0)
      else pure mt
    domains := domains.push liftedMt
    let _ ← TcM.pushFVarDeclAnon liftedMt
  -- Minors, built inline at depth.
  let motiveBase := (← TcM.depth (m := m)).toNat - nMotives
  for h : j in [0:indInfos.size] do
    let jMember := flat[j]!
    for ctorId in indInfos[j].2.2.2.1 do
      let minorTy ← buildMinorAtDepth j ctorId jMember nParams motiveBase
        flat blockAddrs
      domains := domains.push minorTy
      let _ ← TcM.pushFVarDeclAnon minorTy
  -- Indices for THIS member.
  let diMember := flat[di]!
  let mut ity ← TcM.instantiateUnivParams indInfos[di]!.2.2.2.2
    diMember.occurrenceUs
  for j in [0:diMember.ownParams.toNat] do
    let w ← whnf ity
    match w with
    | .all _ _ _ body _ =>
      let p ← if !diMember.isAux then
          let depth ← TcM.depth (m := m)
          pure (KExpr.mkVar (depth - 1 - j.toUInt64) anonN)
        else if j < diMember.specParams.size then
          let sp := diMember.specParams[j]!
          let depth := (← TcM.depth (m := m)).toNat
          let liftBy := depth - min depth nParams
          if liftBy > 0 then TcM.runIntern (lift sp liftBy.toUInt64 0)
          else pure sp
        else
          let depth ← TcM.depth (m := m)
          pure (KExpr.mkVar (depth - 1 - j.toUInt64) anonN)
      ity ← TcM.runIntern (subst body p 0)
    | _ => break
  for _ in [0:nIndices] do
    let w ← whnf ity
    match w with
    | .all _ _ dom body _ =>
      domains := domains.push dom
      let _ ← TcM.pushFVarDeclAnon dom
      ity := body
    | _ => break
  -- Major premise.
  let indId := indInfos[di]!.1
  let mut majorDom ← TcM.intern (.mkConst indId diMember.occurrenceUs)
  let depth := (← TcM.depth (m := m)).toNat
  if !diMember.isAux then
    for i in [0:diMember.ownParams.toNat] do
      let pvar ← TcM.intern (m := m) (.mkVar (depth - 1 - i).toUInt64 anonN)
      majorDom ← TcM.intern (.mkApp majorDom pvar)
  else
    let liftBy := depth - min depth nParams
    for sp in diMember.specParams do
      let lifted ← if liftBy > 0 then TcM.runIntern (lift sp liftBy.toUInt64 0)
        else pure sp
      majorDom ← TcM.intern (.mkApp majorDom lifted)
  for i in [0:nIndices] do
    let ivar ← TcM.intern (m := m) (.mkVar (nIndices - 1 - i).toUInt64 anonN)
    majorDom ← TcM.intern (.mkApp majorDom ivar)
  domains := domains.push majorDom
  let _ ← TcM.pushFVarDeclAnon majorDom
  -- Return: motive_di indices major.
  let depth2 := (← TcM.depth (m := m)).toNat
  let motiveVarIdx := (depth2 - 1 - nParams - di).toUInt64
  let mut ret ← TcM.intern (m := m) (.mkVar motiveVarIdx anonN)
  for i in [0:nIndices] do
    let ivar ← TcM.intern (m := m) (.mkVar (nIndices - i).toUInt64 anonN)
    ret ← TcM.intern (.mkApp ret ivar)
  ret ← TcM.intern (.mkApp ret (← TcM.intern (m := m) (.mkVar 0 anonN)))
  -- Fold the forall chain (inside-out; pop locals).
  for i in [0:domains.size] do
    modify fun s => { s with lctx := s.lctx.truncate (s.lctx.size - 1) }
    ret ← TcM.intern
      (.mkAll anonN anonBi domains[domains.size - 1 - i]! ret)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  return ret

/-- Extract the major-premise domain whose head is `targetAddr`, after
    skipping `prefixSkip` foralls (scan bounded at 64). -/
def recursorMajorDomainForAddr (recTy : KExpr m)
    (prefixSkip : UInt64) (targetAddr : Address) :
    RecM m (Option (KExpr m)) := do
  let mut ty := recTy
  for _ in [0:prefixSkip.toNat] do
    let w ← whnf ty
    match w with
    | .all _ _ _ body _ => ty := body
    | _ => return none
  for _ in [0:65] do
    let w ← whnf ty
    match w with
    | .all _ _ dom body _ =>
      let (head, _) := dom.collectSpine
      match head with
      | .const id _ _ =>
        if id.addr == targetAddr then
          if let some (.indc ..) ← TcM.tryGetConst id then
            return some dom
        ty := body
      | _ => ty := body
    | _ => return none
  return none

/-- Same head/universes/arg-count with def-eq args. -/
def majorDomainSignatureEq (a b : KExpr m) : RecM m Bool := do
  let (aHead, aArgs) := a.collectSpine
  let (bHead, bArgs) := b.collectSpine
  match aHead, bHead with
  | .const aId aUs _, .const bId bUs _ =>
    if aId.addr != bId.addr || aUs.size != bUs.size
        || aArgs.size != bArgs.size then
      return false
    for i in [0:aUs.size] do
      if !univEq aUs[i]! bUs[i]! then
        return false
    for i in [0:aArgs.size] do
      if !(← isDefEq aArgs[i]! bArgs[i]!) then
        return false
    return true
  | _, _ => return false

/-- Position-by-position peer recursor alignment (canonical order both
    sides); `none` on any sanity-check failure. -/
def findPeerRecursors (blockId : KId m)
    (flat : Array (FlatBlockMember m)) : RecM m (Option (Array (KId m))) := do
  let some members ← TcM.tryGetBlock blockId | return none
  let mut recIds : Array (KId m) := #[]
  for id in members do
    if let some (.recr ..) ← TcM.tryGetConst id then
      recIds := recIds.push id
  if recIds.size != flat.size then
    return none
  let mut result : Array (KId m) := Array.mkEmpty flat.size
  for h : fi in [0:flat.size] do
    let member := flat[fi]
    let recId := recIds[fi]!
    let (params, motives, minors, indices, ty) ←
      match (← TcM.tryGetConst recId) with
      | some (.recr (params := p) (motives := mo) (minors := mi)
          (indices := ix) (ty := ty) ..) => pure (p, mo, mi, ix, ty)
      | _ => return none
    let skip ← checkedMetadataSum "recursor major index"
      #[params, motives, minors, indices]
    let majorId? ← try
        pure (some (← getMajorInductiveId ty skip))
      catch
        | .unknownConst a => throw (.unknownConst a)
        | _ => pure none
    let some majorId := majorId? | return none
    if majorId.addr != member.id.addr then
      return none
    if !member.isAux then
      result := result.push recId
      continue
    -- Aux: verify spec_params against the stored major's param args.
    let saved := (← get).lctx.size
    let mut cur := ty
    for _ in [0:skip.toNat] do
      match (← try? (whnf cur)) with
      | some (.all _ _ dom b _) =>
        let _ ← TcM.pushFVarDeclAnon dom
        cur := b
      | _ => break
    let mut matched := false
    match (← try? (whnf cur)) with
    | some (.all _ _ dom _ _) =>
      let (_, majorArgs) := dom.collectSpine
      let nPar := member.ownParams.toNat
      if majorArgs.size ≥ nPar && member.specParams.size == nPar then
        let nRecParams64 := (flat[0]?.map (·.ownParams)).getD 0
        let liftBy := (← TcM.depth (m := m)) -
          min (← TcM.depth (m := m)) nRecParams64
        matched := true
        for i in [0:nPar] do
          let spLifted ← if liftBy > 0 then
              TcM.runIntern (lift member.specParams[i]! liftBy 0)
            else pure member.specParams[i]!
          if !(← isDefEq majorArgs[i]! spLifted) then
            matched := false
            break
    | _ => pure ()
    modify fun s => { s with lctx := s.lctx.truncate saved }
    if !matched then
      return none
    result := result.push recId
  return some result

/-- IH value for a recursive field in a rule RHS:
    `λ xs…, rec[target] params motives minors idxArgs (field xs…)`. -/
def buildRuleIh (fieldIdx nFields totalLams : UInt64)
    (targetBi : Nat) (flat : Array (FlatBlockMember m))
    (peerRecs : Array (KId m)) (nRecParams nMotives nMinors : Nat)
    (isLarge : Bool) (dom : KExpr m) : RecM m (KExpr m) := do
  let targetNParams := flat[targetBi]!.ownParams.toNat
  let peerRec := peerRecs[targetBi]!
  let peerRecLvls ← match (← TcM.tryGetConst peerRec) with
    | some (.recr (lvls := lvls) ..) => pure lvls
    | _ =>
      if isLarge then
        checkedMetadataSum "generated recursor universe arity"
          #[flat[targetBi]!.lvls, 1]
      else
        pure flat[targetBi]!.lvls
  let mut recLvls : Array (KUniv m) := Array.mkEmpty peerRecLvls.toNat
  for i in [0:peerRecLvls.toNat] do
    recLvls := recLvls.push (← TcM.internUniv (m := m) (.mkParam i.toUInt64 anonN))
  -- Peel foralls (stop when the result head is a flat member).
  let wdom ← whnf dom
  let (forallDoms, inner) := peelRuleIhForalls wdom flat
  let nXs := forallDoms.size.toUInt64
  let innerW ← whnf inner
  let (_, innerArgs) := innerW.collectSpine
  let idxArgs := innerArgs.extract targetNParams innerArgs.size
  let depth ← checkedMetadataSum "generated recursor induction-hypothesis depth"
    #[totalLams, nXs]
  let mut ih ← TcM.intern (.mkConst peerRec recLvls)
  for pi in [0:nRecParams] do
    ih ← TcM.intern (.mkApp ih (← TcM.intern (m := m)
      (.mkVar (depth - 1 - pi.toUInt64) anonN)))
  for mi in [0:nMotives] do
    ih ← TcM.intern (.mkApp ih (← TcM.intern (m := m)
      (.mkVar (depth - 1 - nRecParams.toUInt64 - mi.toUInt64) anonN)))
  for mi in [0:nMinors] do
    ih ← TcM.intern (.mkApp ih (← TcM.intern (m := m)
      (.mkVar (depth - 1 - nRecParams.toUInt64 - nMotives.toUInt64
        - mi.toUInt64) anonN)))
  for idx in idxArgs do
    ih ← TcM.intern (.mkApp ih idx)
  let fieldOffset := nFields - 1 - fieldIdx
  let fieldBase ← checkedMetadataSum "generated recursor wrapped-field index"
    #[fieldOffset, nXs]
  let mut fieldApp ← TcM.intern (m := m) (.mkVar fieldBase anonN)
  for xi in [0:nXs.toNat] do
    fieldApp ← TcM.intern (.mkApp fieldApp (← TcM.intern (m := m)
      (.mkVar (nXs - 1 - xi.toUInt64) anonN)))
  ih ← TcM.intern (.mkApp ih fieldApp)
  for i in [0:forallDoms.size] do
    ih ← TcM.intern
      (.mkLam anonN anonBi forallDoms[forallDoms.size - 1 - i]! ih)
  return ih

/-- Rule RHS for one constructor:
    `λ params motives minors fields, minor[gi] fields ihs`. -/
def buildRuleRhs (memberIdx ctorLocalIdx : Nat) (ctorId : KId m)
    (member : FlatBlockMember m) (flat : Array (FlatBlockMember m))
    (peerRecs : Array (KId m)) (recTyForMember : KExpr m)
    (nRecParams : Nat) (isLarge : Bool) : RecM m (KExpr m) := do
  let ctorTyRaw ← match (← TcM.getConst ctorId) with
    | .ctor (ty := ty) .. => pure ty
    | _ => throw (.other "build_rule_rhs: ctor not found")
  let saved := (← get).lctx.size
  let nMotives := flat.size
  let nMinors := flat.foldl (fun acc mem => acc + mem.ctors.size) 0
  let pmm := nRecParams + nMotives + nMinors
  let pmm64 ← checkedNatMetadataSum
    "generated recursor params + motives + minors"
    #[nRecParams, nMotives, nMinors]
  -- Pass 1: count fields.
  let ctorTyInst ← TcM.instantiateUnivParams ctorTyRaw member.occurrenceUs
  let mut countTy := ctorTyInst
  for _ in [0:member.ownParams.toNat] do
    let w ← whnf countTy
    match w with
    | .all _ _ _ body _ => countTy := body
    | _ => break
  let nFields ← runBounded (fun (tmp, nFields) => do
    let w ← whnf tmp
    match w with
    | .all _ _ _ body _ =>
      return .next (body, nFields + 1)
    | _ => return .done nFields) maxWhnfFuel.toNat
      (countTy, (0 : UInt64))
  let totalLams ← checkedMetadataSum "generated recursor rule lambdas"
    #[pmm64, nFields]
  -- Pass 2: body = minor[globalIdx] fields ihs.
  let globalMinorIdx := (flat.extract 0 memberIdx).foldl
    (fun acc mem => acc + mem.ctors.size) 0 + ctorLocalIdx
  if globalMinorIdx ≥ nMinors then
    throw (.other "generated recursor global minor index out of range")
  let minorVarIdx ← checkedNatMetadataSum
    "generated recursor minor variable index"
    #[nFields.toNat, nMinors - 1 - globalMinorIdx]
  let mut body ← TcM.intern (m := m) (.mkVar minorVarIdx anonN)
  for fi in [0:nFields.toNat] do
    body ← TcM.intern (.mkApp body (← TcM.intern (m := m)
      (.mkVar (nFields - 1 - fi.toUInt64) anonN)))
  -- Walk ctor type substituting params to final-lambda positions.
  let auxSpLift := totalLams - min totalLams nRecParams.toUInt64
  let mut ty2 := ctorTyInst
  for j in [0:member.ownParams.toNat] do
    let w ← whnf ty2
    match w with
    | .all _ _ _ body2 _ =>
      let p ← if !member.isAux then
          pure (KExpr.mkVar (totalLams - 1 - j.toUInt64) anonN)
        else if j < member.specParams.size then
          TcM.runIntern (lift member.specParams[j]! auxSpLift 0)
        else
          pure (KExpr.mkVar (totalLams - 1 - j.toUInt64) anonN)
      ty2 ← TcM.runIntern (subst body2 p 0)
    | _ => break
  -- Recursive fields → IH applications.
  let recFieldLift := totalLams - min totalLams nRecParams.toUInt64
  let (_, _, bodyAfterFields) ← runBounded
      (fun (fieldTy, fieldIdx, loopBody) => do
    let w ← whnf fieldTy
    match w with
    | .all _ _ dom body2 _ =>
      let mut loopBody := loopBody
      if let some targetBi ← isRecField dom flat recFieldLift then
        let ih ← buildRuleIh fieldIdx nFields totalLams targetBi flat
          peerRecs nRecParams nMotives nMinors isLarge dom
        loopBody ← TcM.intern (.mkApp loopBody ih)
      let fvar : KExpr m := .mkVar (nFields - 1 - fieldIdx) anonN
      let fieldTy ← TcM.runIntern (subst body2 fvar 0)
      return .next (fieldTy, fieldIdx + 1, loopBody)
    | _ => return .done (fieldTy, fieldIdx, loopBody))
      maxWhnfFuel.toNat (ty2, (0 : UInt64), body)
  body := bodyAfterFields
  -- Field lambdas: domains from the peer recursor's minor premise.
  let minorDomain ← do
    let mut cur := recTyForMember
    let skipToMinor := nRecParams + nMotives + globalMinorIdx
    for _ in [0:skipToMinor] do
      let w ← whnf cur
      match w with
      | .all _ _ _ b _ => cur := b
      | _ => break
    let w ← whnf cur
    match w with
    | .all _ _ dom _ _ => pure dom
    | _ => pure (KExpr.mkSort .mkZero)
  let fieldDomLift ← checkedNatMetadataSum
    "generated recursor field-domain lift" #[nMinors - globalMinorIdx]
  let mut fieldDomains : Array (KExpr m) := Array.mkEmpty nFields.toNat
  let mut minorCur := minorDomain
  for fi in [0:nFields.toNat] do
    let w ← whnf minorCur
    match w with
    | .all _ _ dom b _ =>
      let liftedDom ← if fieldDomLift > 0 then
          TcM.runIntern (lift dom fieldDomLift fi.toUInt64)
        else pure dom
      fieldDomains := fieldDomains.push liftedDom
      minorCur := b
    | _ => break
  for i in [0:fieldDomains.size] do
    body ← TcM.intern
      (.mkLam anonN anonBi fieldDomains[fieldDomains.size - 1 - i]! body)
  -- PMM lambdas from the recursor type's leading domains.
  let mut pmmDomains : Array (KExpr m) := Array.mkEmpty pmm
  let mut recTyCur := recTyForMember
  for _ in [0:pmm] do
    let w ← whnf recTyCur
    match w with
    | .all _ _ dom b _ =>
      pmmDomains := pmmDomains.push dom
      recTyCur := b
    | _ =>
      pmmDomains := pmmDomains.push (KExpr.mkSort .mkZero)
      break
  for i in [0:pmm] do
    let dom := pmmDomains[pmm - 1 - i]?.getD (KExpr.mkSort .mkZero)
    body ← TcM.intern (.mkLam anonN anonBi dom body)
  modify fun s => { s with lctx := s.lctx.truncate saved }
  return body

/-- Generate recursors for every flat member of an inductive block and
    cache them (`recursorCache`, `recMajorsCache`). -/
def generateBlockRecursors (blockId : KId m) : RecM m Unit := do
  let blockInds ← discoverBlockInductives blockId
  if blockInds.isEmpty then
    modify fun s => { s with env := { s.env with
      recursorCache := s.env.recursorCache.insert blockId #[] } }
    return ()
  let mut indInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m) := #[]
  let mut nParams : UInt64 := 0
  let (blockLvls, blockIsUnsafe) ← match (← TcM.getConst blockInds[0]!) with
    | .indc (lvls := lvls) (isUnsafe := isUnsafe) .. =>
      pure (lvls, isUnsafe)
    | _ => throw (.other "generate_block_recursors: not an inductive")
  for h : i in [0:blockInds.size] do
    let indId := blockInds[i]
    match (← TcM.getConst indId) with
    | .indc (params := params) (indices := indices) (ctors := ctors)
        (lvls := lvls) (isUnsafe := isUnsafe) (ty := ty) .. =>
      if i == 0 then
        nParams := params
      if lvls != blockLvls then
        throw (.other "mutual peers must declare the same universe arity")
      if isUnsafe != blockIsUnsafe then
        throw (.other "mutual inductives must share the same safety flag")
      indInfos := indInfos.push (indId, params, indices, ctors, ty)
    | _ => throw (.other "generate_block_recursors: not an inductive")
  let firstIndArity ← checkedMetadataSum "inductive params + indices"
    #[indInfos[0]!.2.1, indInfos[0]!.2.2.1]
  let resultLevel ← getResultSortLevel indInfos[0]!.2.2.2.2
    firstIndArity.toNat
  let isLarge ← isLargeEliminator resultLevel indInfos
  let univOffset : UInt64 := if isLarge then 1 else 0
  let recLvls ← checkedMetadataSum "generated recursor universe arity"
    #[blockLvls, univOffset]
  let elimLevel : KUniv m ← if isLarge then
      TcM.internUniv (m := m) (.mkParam 0 anonN)
    else
      TcM.internUniv (m := m) .mkZero
  let mut flat ← buildFlatBlock blockInds nParams univOffset
  let nOriginals := blockInds.size
  -- Canonicalize the aux portion (compiled envs ship canonical aux order).
  if (← get).env.recursorAuxOrder == .canonical
      && flat.size > nOriginals + 1 then
    let blockUs := flat[0]!.occurrenceUs
    let all0Name := blockInds[0]? >>= (Mode.get? ·.name)
    let canonicalOrder ← canonicalAuxOrder (flat.extract nOriginals flat.size)
      nParams blockUs all0Name blockInds[0]?
    let auxPart := flat.extract nOriginals flat.size
    let mut newAux : Array (FlatBlockMember m) :=
      Array.mkEmpty canonicalOrder.size
    for origIdx in canonicalOrder do
      newAux := newAux.push auxPart[origIdx]!
    flat := flat.extract 0 nOriginals ++ newAux
  -- Flat ind_infos (aux types from env).
  let mut flatIndInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m) :=
    Array.mkEmpty flat.size
  for mem in flat do
    let ty := (← TcM.getConst mem.id).ty
    flatIndInfos := flatIndInfos.push
      (mem.id, mem.ownParams, mem.nIndices, mem.ctors, ty)
  let flatIds := flat.map (·.id)
  -- Motives for ALL flat members.
  let mut motiveTypes : Array (KExpr m) := Array.mkEmpty flat.size
  for mem in flat do
    motiveTypes := motiveTypes.push
      (← buildMotiveTypeFlat mem nParams.toNat elimLevel)
  -- Recursor types for every flat member.
  let nMotives := flat.size.toUInt64
  let nMinors ← checkedMetadataSum "generated recursor minors"
    (flat.map fun mem => mem.ctors.size.toUInt64)
  let mut generated : Array (GeneratedRecursor m) := Array.mkEmpty flat.size
  for di in [0:flat.size] do
    let recType ← buildRecType di flatIndInfos flatIds flat motiveTypes
      univOffset
    generated := generated.push
      { indAddr := flat[di]!.id.addr
        lvls := recLvls
        params := nParams
        motives := nMotives
        minors := nMinors
        indices := flat[di]!.nIndices
        isUnsafe := blockIsUnsafe
        ty := recType
        rules := #[] }
  -- Rules from co-resident peer recursors (when alignment sanity holds).
  let peerRecs ← findPeerRecursors blockId flat
  if let some peers := peerRecs then
    for h : gi in [0:generated.size] do
      let member := flat[gi]!
      let mut rules : Array (Option (RecRule m)) := #[]
      for h2 : ci in [0:member.ctors.size] do
        let ctorId := member.ctors[ci]
        let ctorFields ← match (← TcM.getConst ctorId) with
          | .ctor (fields := fields) .. => pure fields
          | _ => throw (.other "generate_block_recursors: ctor not found")
        let recTy := generated[gi]!.ty
        let rhs? ← try?
          (buildRuleRhs gi ci ctorId member flat peers recTy nParams.toNat
            isLarge)
        match rhs? with
        | some rhs =>
          rules := rules.push (some ⟨ctorId.name, ctorFields, rhs⟩)
        | none => rules := rules.push none
      if rules.all (·.isSome) then
        let done := rules.filterMap id
        generated := generated.modify gi fun g => { g with rules := done }
  -- Majors cache: sorted flat-member ids → block.
  let majorsKey := sortedDedupIds flatIds
  modify fun s => { s with env := { s.env with
    recMajorsCache := s.env.recMajorsCache.insert majorsKey blockId,
    recursorCache := s.env.recursorCache.insert blockId generated } }

/-- Populate canonical rules from the recursor block's peers (block-level
    recursor checking path). Verifies canonical alignment peer-by-peer via
    major-domain signatures; a divergence is a hard error. -/
def populateRecursorRulesFromBlock (indBlockId recBlockId : KId m) :
    RecM m Unit := do
  let some generatedSnapshot := (← get).env.recursorCache[indBlockId]?
    | return ()
  if generatedSnapshot.isEmpty then
    return ()
  let some members ← TcM.tryGetBlock recBlockId | return ()
  let mut recIds : Array (KId m) := #[]
  for id in members do
    if let some (.recr ..) ← TcM.tryGetConst id then
      recIds := recIds.push id
  if recIds.isEmpty then
    return ()
  let blockInds ← discoverBlockInductives indBlockId
  if blockInds.isEmpty then
    return ()
  let nParams64 ← match (← TcM.tryGetConst blockInds[0]!) with
    | some (.indc (params := params) ..) => pure params
    | _ => return ()
  let indLvls ← match (← TcM.tryGetConst blockInds[0]!) with
    | some (.indc (lvls := lvls) ..) => pure lvls
    | _ => pure 0
  let univOffset : UInt64 ← match recIds[0]? with
    | some rid =>
      match (← TcM.tryGetConst (m := m) rid) with
      | some (.recr (lvls := lvls) ..) => pure (if lvls > indLvls then (1 : UInt64) else 0)
      | _ => pure 0
    | none => pure 0
  let mut flat ← buildFlatBlock blockInds nParams64 univOffset
  let nOriginals := blockInds.size
  if (← get).env.recursorAuxOrder == .canonical
      && flat.size > nOriginals + 1 then
    let blockUs := flat[0]!.occurrenceUs
    let all0Name := blockInds[0]? >>= (Mode.get? ·.name)
    let canonicalOrder ← canonicalAuxOrder (flat.extract nOriginals flat.size)
      nParams64 blockUs all0Name blockInds[0]?
    let auxPart := flat.extract nOriginals flat.size
    let mut newAux : Array (FlatBlockMember m) :=
      Array.mkEmpty canonicalOrder.size
    for origIdx in canonicalOrder do
      newAux := newAux.push auxPart[origIdx]!
    flat := flat.extract 0 nOriginals ++ newAux
  if flat.size != generatedSnapshot.size then
    throw (.other s!"populate_recursor_rules_from_block: flat/generated length mismatch: flat={flat.size} generated={generatedSnapshot.size}")
  if (generatedSnapshot.zip flat).all
      (fun (g, mem) => g.rules.size == mem.ctors.size) then
    return ()
  let nMotives := flat.size.toUInt64
  let nMinors ← checkedMetadataSum "generated recursor minors"
    (flat.map fun mem => mem.ctors.size.toUInt64)
  let prefixBase ← checkedMetadataSum
    "generated recursor params + motives + minors"
    #[nParams64, nMotives, nMinors]
  if recIds.size != flat.size then
    throw (.other s!"populate_recursor_rules_from_block: rec_ids/flat count mismatch: rec_ids={recIds.size} flat={flat.size}")
  -- Verify canonical alignment via major-domain signatures.
  let mut peers : Array (KId m) := Array.mkEmpty flat.size
  for h : gi in [0:generatedSnapshot.size] do
    let genRec := generatedSnapshot[gi]
    let targetAddr := genRec.indAddr
    let rid := recIds[gi]!
    let (params, motives, minors, indices, ty) ←
      match (← TcM.getConst rid) with
      | .recr (params := p) (motives := mo) (minors := mi) (indices := ix)
          (ty := ty) .. => pure (p, mo, mi, ix, ty)
      | _ => throw (.other s!"populate_recursor_rules_from_block: rec_ids[{gi}]={rid} is not a recursor")
    let genSkip ← checkedMetadataSum "generated recursor major index"
      #[prefixBase, flat[gi]!.nIndices]
    let genMajor ← recursorMajorDomainForAddr genRec.ty genSkip targetAddr
    let storedSkip ← checkedMetadataSum "recursor major index"
      #[params, motives, minors, indices]
    let storedMajor ← recursorMajorDomainForAddr ty storedSkip targetAddr
    let signaturesMatch ← match genMajor, storedMajor with
      | some g, some s => majorDomainSignatureEq g s
      | _, _ => pure false
    if !signaturesMatch then
      throw (.other s!"populate_recursor_rules_from_block: canonical-order mismatch at peer {gi}")
    peers := peers.push rid
  let isLarge := univOffset > 0
  let mut generatedWithRules := generatedSnapshot
  for h : gi in [0:flat.size] do
    let member := flat[gi]
    let recTyForMember := generatedWithRules[gi]!.ty
    let mut rules : Array (RecRule m) := Array.mkEmpty member.ctors.size
    for h2 : ci in [0:member.ctors.size] do
      let ctorId := member.ctors[ci]
      let ctorFields ← match (← TcM.getConst ctorId) with
        | .ctor (fields := fields) .. => pure fields
        | _ => throw (.other "populate_recursor_rules_from_block: ctor not found")
      let rhs ← buildRuleRhs gi ci ctorId member flat peers recTyForMember
        nParams64.toNat isLarge
      rules := rules.push ⟨ctorId.name, ctorFields, rhs⟩
    generatedWithRules := generatedWithRules.modify gi
      fun g => { g with rules }
  -- Store rules back.
  let some cached := (← get).env.recursorCache[indBlockId]?
    | return ()
  if cached.size != generatedWithRules.size then
    throw (.other s!"populate_recursor_rules_from_block: cache changed length: cached={cached.size} generated={generatedWithRules.size}")
  let merged := cached.zipWith (fun dst src => { dst with rules := src.rules })
    generatedWithRules
  modify fun s => { s with env := { s.env with
    recursorCache := s.env.recursorCache.insert indBlockId merged } }

-- ### Recursor checking

/-- Major inductive ids of all peer recursors in a block, sorted+deduped
    (Rust `BTreeSet<KId>` key). -/
def gatherPeerMajors (recBlock : KId m) : RecM m (Array (KId m)) := do
  let mut peers : Array (KId m) := #[]
  match (← TcM.tryGetBlock recBlock) with
  | some members =>
    for id in members do
      if let some (.recr ..) ← TcM.tryGetConst id then
        peers := peers.push id
  | none => pure ()
  let mut majors : Array (KId m) := #[]
  for peerId in peers do
    let (p, mo, mi, ix, peerTy) ← match (← TcM.getConst peerId) with
      | .recr (params := p) (motives := mo) (minors := mi) (indices := ix)
          (ty := ty) .. => pure (p, mo, mi, ix, ty)
      | _ => continue
    let skip ← checkedMetadataSum "recursor major index" #[p, mo, mi, ix]
    let major? ← try
        pure (some (← getMajorInductiveId peerTy skip))
      catch
        | .unknownConst a => throw (.unknownConst a)
        | _ => pure none
    if let some major := major? then
      majors := majors.push major
  return sortedDedupIds majors

/-- Block-coordinated inductive validation (inductive.rs `check_inductive`):
    pure inductive blocks route through `blockCheckResults`; anything else
    falls back to the member check. -/
def checkInductive (id : KId m) : RecM m Unit := do
  let block ← match (← TcM.getConst id) with
    | .indc (block := block) .. => pure block
    | _ => throw (.other "check_inductive: not an inductive")
  let some members ← TcM.tryGetBlock block
    | return (← checkInductiveMemberImpl id)
  for member in members do
    match (← TcM.tryGetConst member) with
    | some (.indc ..) | some (.ctor ..) => pure ()
    | _ => return (← checkInductiveMemberImpl id)
  if let some result := (← get).env.blockCheckResults[block]? then
    match result with
    | .ok () => return ()
    | .error e => throw e
  let result ←
    try
      checkInductiveBlockImpl block members
      pure (Except.ok ())
    catch e =>
      pure (Except.error e)
  modify fun s => { s with env := { s.env with
    blockCheckResults := s.env.blockCheckResults.insert block result } }
  match result with
  | .ok () => return ()
  | .error e => throw e

/-- Validate a recursor against the generated canonical form (type def-eq +
    per-rule field count and RHS def-eq), with signature-based aux
    disambiguation. Every successful path compares both type and rules. -/
def checkRecursorMemberImpl (id : KId m) : RecM m Unit := do
  let (recBlock, ty, declaredK, declaredLvls, declaredIsUnsafe, params,
      motives, minors, indices) ←
    match (← TcM.getConst id) with
    | .recr (block := block) (ty := ty) (k := k) (params := p)
        (lvls := lvls) (isUnsafe := isUnsafe) (motives := mo)
        (minors := mi) (indices := ix) .. =>
      pure (block, ty, k, lvls, isUnsafe, p, mo, mi, ix)
    | _ => throw (.other "check_recursor: not a recursor")
  let skip ← checkedMetadataSum "recursor major index"
    #[params, motives, minors, indices]
  let indId ← getMajorInductiveId ty skip
  -- Coherence gate: the major inductive must itself pass A1–A4.
  if let some (.indc ..) ← TcM.tryGetConst indId then
    checkInductive indId
  let indBlock ← match (← TcM.tryGetConst indId) with
    | some (.indc (block := block) ..) => pure (some block)
    | _ => pure none
  -- Direct block lookup needs enough motives (aux recursors overflow it).
  let resolvedBlock? ← match indBlock with
    | some ib =>
      match (← get).env.recursorCache[ib]? with
      | some cached =>
        if cached.size.toUInt64 ≥ motives then pure (some ib) else pure none
      | none => pure none
    | none => pure none
  let resolvedBlock ← match resolvedBlock? with
    | some b => pure b
    | none =>
      let majorsKey ← gatherPeerMajors recBlock
      match (← get).env.recMajorsCache[majorsKey]? with
      | some blockId => pure blockId
      | none =>
        -- Generate from each peer major's block, then re-check.
        for majorId in majorsKey do
          if let some (.indc (block := block) ..) ← TcM.tryGetConst majorId then
            if !(← get).env.recursorCache.contains block then
              let _ ← try? (generateBlockRecursors block)
        let majorsKey2 ← gatherPeerMajors recBlock
        match (← get).env.recMajorsCache[majorsKey2]? with
        | some blockId => pure blockId
        | none => throw (.other "check_recursor: could not resolve inductive block")
  -- S1: constructive K verification.
  let computedK ← computeKTarget indId
  if declaredK != computedK then
    throw (.other s!"check_recursor: K-target mismatch: declared k={declaredK}, computed k={computedK}")
  populateRecursorRulesFromBlock resolvedBlock recBlock
  let some generated := (← get).env.recursorCache[resolvedBlock]?
    | throw (.other "check_recursor: no generated recursors")
  -- Signature-first selection (dedups aux recursors sharing a major head).
  let storedPos := (← get).env.blocks[recBlock]?.bind
    (·.findIdx? (fun mem => mem == id))
  let prefixSkip ← checkedMetadataSum "recursor params + motives + minors"
    #[params, motives, minors]
  let storedMajor ← recursorMajorDomainForAddr ty prefixSkip indId.addr
  let mut signatureMatches : Array Nat := #[]
  if let some storedMajorD := storedMajor then
    for h : gi in [0:generated.size] do
      let g := generated[gi]
      if g.indAddr != indId.addr then
        continue
      if let some genMajor ← recursorMajorDomainForAddr g.ty prefixSkip
          g.indAddr then
        if ← majorDomainSignatureEq genMajor storedMajorD then
          signatureMatches := signatureMatches.push gi
  let selectedIdx :=
    (storedPos.bind (fun p => signatureMatches.find? (· == p)))
    <|> signatureMatches[0]?
    <|> (storedPos.filter (· < generated.size))
    <|> (generated.findIdx? (·.indAddr == indId.addr))
  match selectedIdx.bind (generated[·]?) with
  | some g =>
    if declaredLvls != g.lvls then
      throw (.other s!"check_recursor: universe arity mismatch: stored={declaredLvls}, generated={g.lvls}")
    if declaredIsUnsafe != g.isUnsafe then
      throw (.other s!"check_recursor: safety mismatch: stored={declaredIsUnsafe}, generated={g.isUnsafe}")
    if params != g.params || motives != g.motives || minors != g.minors
        || indices != g.indices then
      throw (.other s!"check_recursor: arity metadata mismatch: stored=(params={params}, motives={motives}, minors={minors}, indices={indices}), generated=(params={g.params}, motives={g.motives}, minors={g.minors}, indices={g.indices})")
    if !(← isDefEq g.ty ty) then
      throw (.other "check_recursor: type mismatch")
    let genRules := g.rules
    let storedRules ← match (← TcM.getConst id) with
      | .recr (rules := rules) .. => pure rules
      | _ => pure #[]
    if genRules.isEmpty && !storedRules.isEmpty then
      -- C1: cannot verify stored rules against a missing canonical form.
      throw (.other s!"check_recursor: rule generation failed, cannot verify {storedRules.size} stored rules")
    else if !genRules.isEmpty && storedRules.isEmpty then
      throw (.other s!"check_recursor: stored recursor has no rules (expected {genRules.size})")
    else if genRules.size != storedRules.size then
      throw (.other s!"check_recursor: rule count mismatch: gen={genRules.size} stored={storedRules.size}")
    for h : ri in [0:genRules.size] do
      let genRule := genRules[ri]
      let storedRule := storedRules[ri]!
      if genRule.fields != storedRule.fields then
        throw (.other s!"check_recursor: rule {ri} field count mismatch: gen={genRule.fields} stored={storedRule.fields}")
      if !(← isDefEq genRule.rhs storedRule.rhs) then
        throw (.other s!"check_recursor: rule {ri} RHS mismatch")
  | none =>
    -- C2: no generated recursor — MUST NOT silently pass.
    throw (.other "check_recursor: no generated recursor for major")

/-- Validate every recursor in a homogeneous recursor block. -/
def checkRecursorBlockImpl (block : KId m)
    (members : Array (KId m)) : RecM m Unit := do
  for member in members do
    TcM.reset (m := m)
    let c ← TcM.getConst member
    validateConstWellScoped c
    match c with
    | .recr (ty := ty) .. =>
      let t ← infer ty
      let _ ← ensureSortDirect t
    | _ =>
      throw (.other s!"check_recursor_block: non-recursor member {member} in block {block}")
  for member in members do
    TcM.reset (m := m)
    checkRecursorMemberImpl member

end

end RecM

end Ix.Tc

end
end
