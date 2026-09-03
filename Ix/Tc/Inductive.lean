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

/-- Canonical generated-recursor header for one member at its exact position
    in the validated flat block.  Block-wide values are supplied once; family
    address, motive count, and index count are read from the flat block itself. -/
def FlatBlockMember.generatedRecursorMetadata
    (member : FlatBlockMember m) (flat : Array (FlatBlockMember m))
    (recLvls nParams nMinors : UInt64) (blockIsUnsafe : Bool) :
    GeneratedRecursorMetadata :=
  { indAddr := member.id.addr
    lvls := recLvls
    params := nParams
    motives := flat.size.toUInt64
    minors := nMinors
    indices := member.nIndices
    isUnsafe := blockIsUnsafe }

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

/-- Queue state used while the flat block grows.  The final component records
the exact structural specializations already appended. -/
abbrev FlatBlockQueueState (m : Mode) :=
  Nat × Array (FlatBlockMember m) × Array NestedSpecializationKey

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

/-- The live telescope accumulated immediately before `buildRecType` closes
its forall chain. Naming this boundary exposes the actual per-domain
construction run to the generated-artifact proof. -/
structure GeneratedRecursorTypeBody (m : Mode) where
  saved : Nat
  domains : Array (KExpr m)
  body : KExpr m

/-- Exact checked inputs passed from block preparation to generated recursor
type/rule construction.  Keeping this boundary data-bearing lets verification
retain the production-selected flat block and motive syntax without replaying
a parallel preprocessor. -/
structure GeneratedRecursorBuildInputs (m : Mode) where
  flatIndInfos :
    Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m)
  flatIds : Array (KId m)
  flat : Array (FlatBlockMember m)
  motiveTypes : Array (KExpr m)
  univOffset : UInt64
  recLvls : UInt64
  nParams : UInt64
  nMinors : UInt64
  blockIsUnsafe : Bool
  isLarge : Bool

/-- Immutable stored-declaration data captured before the recursor-member
prelude invokes any recursive method callback.  `majorSkip` is the checked
metadata sum consumed by major-owner discovery; retaining it prevents the
verification trace from reconstructing wrapping arithmetic independently of
production. -/
structure RecursorMemberDeclarationSnapshot (m : Mode) where
  recBlock : KId m
  ty : KExpr m
  declaredK : Bool
  declaredLvls : UInt64
  declaredIsUnsafe : Bool
  params : UInt64
  motives : UInt64
  minors : UInt64
  indices : UInt64
  storedRules : Array (RecRule m)
  majorSkip : UInt64

/-- Frozen data passed from the stateful recursor-member prelude to the final
generated-artifact comparison.  The stored declaration is captured before any
callback, while `generated` is captured only after block resolution, K-target
validation, and transactional rule population have completed.  Keeping both
snapshots in the return value gives verification an exact production boundary
without replaying the prelude in a shadow model. -/
structure PreparedRecursorMemberCheck (m : Mode) where
  recBlock : KId m
  ty : KExpr m
  declaredK : Bool
  declaredLvls : UInt64
  declaredIsUnsafe : Bool
  params : UInt64
  motives : UInt64
  minors : UInt64
  indices : UInt64
  storedRules : Array (RecRule m)
  indId : KId m
  resolvedBlock : KId m
  computedK : Bool
  generated : Array (GeneratedRecursor m)

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

/-- Peel a fixed result-sort telescope while retaining every opened binder in
the legacy local stack.  Naming the recursion exposes the exact temporary
scope to verification; `expected` and `found` preserve the original error
message. -/
def peelResultSortForalls (expected : Nat) :
    Nat → Nat → KExpr m → RecM m (KExpr m)
  | 0, _, ty => pure ty
  | remaining + 1, found, ty => do
      let w ← whnf ty
      match w with
      | .all _ _ dom body _ =>
        TcM.pushLocal dom
        peelResultSortForalls expected remaining (found + 1) body
      | _ =>
        throw (.other
          s!"get_result_sort_level: expected {expected} foralls, only found {found}")

/-- Result-sort discovery while its temporary legacy telescope is live.  The
public wrapper below owns unconditional depth restoration. -/
def getResultSortLevelBody (ty : KExpr m) (n : Nat) :
    RecM m (KUniv m) := do
  let t ← peelResultSortForalls n n 0 ty
  let w ← whnf t
  match w with
  | .sort u _ => pure u
  | _ => throw (.other "get_result_sort_level: not a sort")

/-- Result sort after peeling `n` foralls.  Each open body remains scoped by
the legacy local stack, and the caller depth is restored on every success or
error (including a recursive WHNF failure). -/
def getResultSortLevel (ty : KExpr m) (n : Nat) :
    RecM m (KUniv m) := do
  let saved ← liftM (TcM.saveDepth (m := m))
  try
    getResultSortLevelBody ty n
  finally
    liftM (TcM.restoreDepth (m := m) saved)

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

/-- Open exactly the shared parameter prefix used by strict positivity.
`none` retains production's deliberately permissive short-telescope result:
A1/A2 diagnose that malformed declaration later.  Naming this loop also
ensures the caller's scope-restoration epilogue is not bypassed by an early
`return` from inside a `for` loop. -/
def openPositivityParameters :
    KExpr m → Nat → Array (KExpr m) →
      RecM m (Option (KExpr m × Array (KExpr m)))
  | ty, 0, paramFVars => pure (some (ty, paramFVars))
  | ty, remaining + 1, paramFVars => do
      let w ← whnf ty
      match w with
      | .all _ _ dom body _ =>
        let (open', fv, _) ← TcM.openBinderAnonWithFV dom body
        openPositivityParameters open' remaining (paramFVars.push fv)
      | _ => pure none

/-- One source-ordered field iteration of constructor positivity.  This is
the exact step supplied to `runBounded`; exposing it lets the verification
layer retain the WHNF, domain check, and binder-opening states without adding
runtime instrumentation. -/
def checkPositivityFieldStep (groups : Array (PositivityGroup m))
    (blockAddrs : Array Address) (ty : KExpr m) :
    RecM m (BoundedStep (KExpr m) Unit) := do
  let w ← whnf ty
  match w with
  | .all _ _ dom body _ =>
    checkPositivityDomain dom groups blockAddrs
    let (open', _) ← TcM.openBinderAnon dom body
    return .next open'
  | _ => return .done ()

/-- Protected body of strict positivity before restoration of the caller's
local-context prefix. -/
def checkPositivityCore (ctorTy : KExpr m) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Unit := do
  match ← openPositivityParameters ctorTy nParams (Array.mkEmpty nParams) with
  | none => return ()
  | some (ty, paramFVars) =>
    let groups : Array (PositivityGroup m) :=
      #[{ addrs := blockAddrs, params := paramFVars, concreteUs := none }]
    runBounded (checkPositivityFieldStep groups blockAddrs)
      maxWhnfFuel.toNat ty

/-- A3: strict positivity — block inductives must not appear in negative
    position in any constructor field. -/
def checkPositivity (ctorTy : KExpr m) (nParams : Nat)
    (blockAddrs : Array Address) : RecM m Unit := do
  let saved := (← get).lctx.size
  let result ←
    try
      checkPositivityCore ctorTy nParams blockAddrs
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

/-- Stateless arity guard for an external inductive application reached by
    nested positivity.  Retaining the original combined condition and error
    value makes this definition an exact proof-visible presentation of the
    production branch. -/
def checkNestedPositivityApplicationPreconditions
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (nParams nIndices lvls : Nat) : Except (TcError m) Unit :=
  if args.size != nParams + nIndices || us.size != lvls then
    .error (.other "positivity: malformed nested inductive application")
  else
    .ok ()

/-- First exact nested-family specialization already present on the active
    positivity stack.  Selection is pure: every candidate test is structural,
    so replacing the source `for`/early-return search with `find?` preserves
    both its source order and verdict. -/
def findNestedPositivityGroup? (groups : Array (PositivityGroup m))
    (family : Address) (us : Array (KUniv m))
    (args : Array (KExpr m)) (nParams : Nat) : Option (PositivityGroup m) :=
  groups.find? fun group =>
    group.addrs.contains family &&
      positivityGroupMatches group family us args nParams

/-- Whether the parameter prefix of a fully applied external family contains
    an occurrence of the root block. -/
def nestedParametersMentionRoot (args : Array (KExpr m)) (nParams : Nat)
    (rootAddrs : Array Address) : Bool :=
  (args.extract 0 (min nParams args.size)).any
    (exprMentionsAnyAddr · rootAddrs)

/-- Validate one constructor of a newly discovered nested specialization:
    load the concrete constructor type, then recursively check its fields. -/
def checkNestedConstructorFuel (fuel : Nat) (ctorId : KId m)
    (nParams : Nat)
    (paramArgs : Array (KExpr m)) (us : Array (KUniv m))
    (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) : RecM m Unit := do
  let ctorTy ← match (← TcM.getConst ctorId) with
    | .ctor (ty := ty) .. => pure ty
    | _ => throw (.other "positivity: nested ctor not found")
  checkNestedCtorFieldsFuel fuel ctorTy nParams paramArgs us groups activeAddrs

/-- Traverse every constructor of a newly discovered nested family in source
    order. -/
def checkNestedConstructorsFuel (fuel : Nat) (ctors : Array (KId m))
    (nParams : Nat) (paramArgs : Array (KExpr m))
    (us : Array (KUniv m)) (groups : Array (PositivityGroup m))
    (activeAddrs : Array Address) : RecM m Unit := do
  for ctorId in ctors do
    checkNestedConstructorFuel fuel ctorId nParams paramArgs us groups
      activeAddrs

/-- Traverse a newly discovered nested-family specialization after exact
    specialization absence and parameter/index occurrence guards have passed.
    Block discovery and constructor validation retain their production order. -/
def checkFreshNestedPositivityApplicationFuel (fuel : Nat)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (nParams : Nat) (block : KId m) (ctors : Array (KId m)) : RecM m Unit := do
  -- Augmented address set: block + the external inductive's block.
  let extBlockInductives ← discoverBlockInductives block
  let extAddrs := extBlockInductives.map (·.addr)
  let augmented := activeAddrs ++ extAddrs
  let paramArgs := args.extract 0 (min nParams args.size)
  let augmentedGroups := groups.push
    { addrs := extAddrs, params := paramArgs, concreteUs := some us }
  checkNestedConstructorsFuel fuel ctors nParams paramArgs us augmentedGroups
    augmented

/-- Continue nested positivity after the external inductive header and its
    exact application arities have been validated.  Specialization matching,
    index independence, block discovery, and constructor traversal retain
    their production order. -/
def checkNestedPositivityApplicationCheckedFuel (fuel : Nat) (id : KId m)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (rootAddrs activeAddrs : Array Address)
    (nParams : Nat) (block : KId m)
    (ctors : Array (KId m)) : RecM m Unit := do
  -- Repeated exact specialization closes an already-validated auxiliary
  -- edge. The same address at a different specialization is a new auxiliary,
  -- as in the two Array specializations of Lean.Doc.Block.
  match findNestedPositivityGroup? groups id.addr us args nParams with
  | some _ =>
      if !positiveIndicesIndependent args nParams rootAddrs then
        throw (.other "positivity: recursive occurrence index mentions an active inductive")
  | none =>
      if !nestedParametersMentionRoot args nParams rootAddrs then
        throw (.other "positivity: not a valid inductive app")
      -- Index args (after params) must not mention block inductives.
      if !positiveIndicesIndependent args nParams rootAddrs then
        throw (.other "positivity: index mentions block inductive")
      checkFreshNestedPositivityApplicationFuel fuel us args groups activeAddrs
        nParams block ctors

/-- Continue nested positivity after resolving the exact external inductive
    header.  The stateless arity guard precedes the named checked continuation,
    while all executable specialization, index, discovery, and constructor
    checks remain in their original production order. -/
def checkNestedPositivityApplicationResolvedFuel (fuel : Nat) (id : KId m)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (rootAddrs activeAddrs : Array Address)
    (nParams nIndices lvls : Nat) (block : KId m)
    (ctors : Array (KId m)) : RecM m Unit := do
  match checkNestedPositivityApplicationPreconditions us args nParams nIndices
      lvls with
  | .error err => throw err
  | .ok () =>
      checkNestedPositivityApplicationCheckedFuel fuel id us args groups
        rootAddrs activeAddrs nParams block ctors

/-- Validate and recursively traverse an external inductive application whose
    parameter specialization mentions the root block.  The caller has already
    reduced the field domain to this constant-headed spine and established
    that the head is not a root-family address.  Keeping the lookup and
    resolved continuation as named production actions gives E2c an exact
    successful-header boundary without changing execution order. -/
def checkNestedPositivityApplicationFuel (fuel : Nat) (id : KId m)
    (us : Array (KUniv m)) (args : Array (KExpr m))
    (groups : Array (PositivityGroup m)) (rootAddrs activeAddrs : Array Address) :
    RecM m Unit := do
  match (← TcM.getConst id) with
  | .indc (params := params) (indices := indices) (lvls := lvls)
      (block := block) (ctors := ctors) .. =>
    checkNestedPositivityApplicationResolvedFuel fuel id us args groups
      rootAddrs activeAddrs params.toNat indices.toNat lvls.toNat block ctors
  | _ => throw (.other "positivity: not a valid inductive app")

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
      checkNestedPositivityApplicationFuel fuel id us args groups rootAddrs
        activeAddrs
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

/-- Strip exactly the external family's parameter-binder prefix after
    universe instantiation.  A constructor with fewer binders than its
    family's declared parameter count is malformed: accepting it as an empty
    field telescope would skip the nested positivity obligations entirely. -/
def stripNestedCtorParameters (ty : KExpr m) : Nat → RecM m (KExpr m)
  | 0 => pure ty
  | remaining + 1 => do
      let w ← whnf ty
      match w with
      | .all _ _ _ body _ => stripNestedCtorParameters body remaining
      | _ => throw (.other
          "positivity: nested constructor has fewer parameter binders than declared")

def checkNestedCtorFieldsFuel :
    Nat → KExpr m → Nat → Array (KExpr m) → Array (KUniv m) →
      Array (PositivityGroup m) → Array Address → RecM m Unit
  | 0, _, _, _, _, _, _ => throw .maxRecDepth
  | fuel + 1, ctorTy, nParams, paramArgs, us, groups, activeAddrs => do
  let instantiated ← TcM.instantiateUnivParams ctorTy us
  let stripped ← stripNestedCtorParameters instantiated nParams
  -- Var(0) = innermost = LAST param after stripping; simulSubst maps
  -- Var(i) ↦ substs[i], so reverse the param order.
  let substituted ←
    TcM.runIntern (simulSubst stripped paramArgs.reverse 0)
  checkNestedCtorFieldsLoopFuel fuel substituted groups activeAddrs

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

/-- Complete A1–A4 validation of one constructor after its parent inductive
header and block context have been resolved.  Naming this shared sequence
keeps member-wide and standalone-constructor checking on the same production
path and gives E2c one exact seam at which successful positivity can be
retained before the later universe and return-type checks. -/
def checkInductiveConstructor (ctorId inductId : KId m)
    (expectedCidx indParams indIndices : Nat) (indLvls : UInt64)
    (indIsUnsafe : Bool) (indTy : KExpr m) (indLevel : KUniv m)
    (blockAddrs : Array Address) : RecM m Unit := do
  let (ctorTy, ctorFields) ← checkCtorMetadataAgainstParent ctorId inductId
    expectedCidx indParams indLvls indIsUnsafe
  checkParamAgreement indTy ctorTy indParams
  if !indIsUnsafe then
    checkPositivity ctorTy indParams blockAddrs
  checkFieldUniverses ctorTy indParams indLevel
  checkCtorReturnType ctorTy indParams indIndices ctorFields
    inductId.addr indLvls blockAddrs

/-- Source-ordered constructor traversal for one resolved inductive header.
The list is exactly `ctors.toList`; the explicit index is the canonical
constructor index checked by `checkInductiveConstructor`. -/
def checkInductiveConstructors (inductId : KId m)
    (indParams indIndices : Nat) (indLvls : UInt64)
    (indIsUnsafe : Bool) (indTy : KExpr m) (indLevel : KUniv m)
    (blockAddrs : Array Address) : List (KId m) → Nat → RecM m Unit
  | [], _ => pure ()
  | ctorId :: ctorIds, expectedCidx => do
      checkInductiveConstructor ctorId inductId expectedCidx indParams
        indIndices indLvls indIsUnsafe indTy indLevel blockAddrs
      checkInductiveConstructors inductId indParams indIndices indLvls
        indIsUnsafe indTy indLevel blockAddrs ctorIds (expectedCidx + 1)

/-- S3/S3b agreement for one already-resolved inductive header.  The cache
gate and peer order are unchanged; the named phase lets verification treat
peer agreement as the prefix before the complete constructor traversal. -/
def checkInductivePeerAgreement (id block : KId m)
    (params lvls : UInt64) (isUnsafe : Bool)
    (ty : KExpr m) (indLevel : KUniv m)
    (blockInds : Array (KId m)) : RecM m Unit := do
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

/-- Populate the canonical recursor cache exactly when the resolved block has
not already been generated. -/
def ensureInductiveRecursors (block : KId m) : RecM m Unit := do
  if !(← get).env.recursorCache.contains block then
    generateBlockRecursors block

/-- Validate an already-resolved inductive header: discover its block peers,
establish the result level and peer agreement, validate every constructor,
then populate the canonical recursor cache. -/
def checkResolvedInductiveMember (id : KId m)
    (params indices lvls : UInt64) (ctors : Array (KId m))
    (block : KId m) (isUnsafe : Bool) (ty : KExpr m) : RecM m Unit := do
  let blockInds ← discoverBlockInductives block
  let blockAddrs := blockInds.map (·.addr)
  -- Result sort must exist even for ctor-less inductives.
  let indArity ← checkedMetadataSum "inductive params + indices"
    #[params, indices]
  let indLevel ← getResultSortLevel ty indArity.toNat
  checkInductivePeerAgreement id block params lvls isUnsafe ty
    indLevel blockInds
  checkInductiveConstructors id params.toNat indices.toNat lvls isUnsafe ty
    indLevel blockAddrs ctors.toList 0
  -- Recursor generation for the block (fatal — silent failure would let
  -- an unverifiable recursor slip through).
  ensureInductiveRecursors block

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
  checkResolvedInductiveMember id params indices lvls ctors block isUnsafe ty

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
  let blockInds ← discoverBlockInductives indBlock
  let blockAddrs := blockInds.map (·.addr)
  let indArity ← checkedMetadataSum "inductive params + indices"
    #[indParams, indIndices]
  let indLevel ← getResultSortLevel indTy indArity.toNat
  checkInductiveConstructor ctorId inductId expectedCidx indParams.toNat
    indIndices.toNat indLvls indIsUnsafe indTy indLevel blockAddrs

/-- Validate every inductive and constructor of a homogeneous inductive
block's untouched stored members before consulting any flattened/nested
representation.  The two returned arrays preserve source order. -/
def classifyInductiveBlockMembers (block : KId m) :
    List (KId m) → Array (KId m) → Array (KId m) →
      RecM m (Array (KId m) × Array (KId m))
  | [], indIds, ctorIds => pure (indIds, ctorIds)
  | member :: members, indIds, ctorIds => do
      TcM.reset (m := m)
      let c ← TcM.getConst member
      validateConstWellScoped c
      match c with
      | .indc (ty := ty) .. =>
          let t ← infer ty
          let _ ← ensureSortDirect t
          classifyInductiveBlockMembers block members (indIds.push member)
            ctorIds
      | .ctor (ty := ty) .. =>
          let t ← infer ty
          let _ ← ensureSortDirect t
          classifyInductiveBlockMembers block members indIds
            (ctorIds.push member)
      | _ =>
          throw (.other s!"check_inductive_block: non-inductive member {member} in block {block}")

/-- Source-ordered validation of the inductive headers discovered by the
untouched-member classification pass.  Reset remains immediately before each
member check, exactly as in the original array loop. -/
def checkInductiveMembers : List (KId m) → RecM m Unit
  | [] => pure ()
  | indId :: indIds => do
      TcM.reset (m := m)
      checkInductiveMemberImpl indId
      checkInductiveMembers indIds

/-- Source-ordered standalone validation of the constructors discovered by
the untouched-member classification pass.  Production intentionally reloads
the parent before resetting the per-check state; a non-constructor is skipped
just as by the former loop's `continue`. -/
def checkInductiveConstructorMembers : List (KId m) → RecM m Unit
  | [] => pure ()
  | ctorId :: ctorIds => do
      match (← TcM.getConst ctorId) with
      | .ctor (induct := induct) .. =>
          TcM.reset (m := m)
          checkCtorAgainstInductiveMemberImpl ctorId induct
      | _ => pure ()
      checkInductiveConstructorMembers ctorIds

/-- Validate every inductive and constructor of a homogeneous inductive
    block: per-member well-scopedness + type inference, then the member
    checks. -/
def checkInductiveBlockImpl (block : KId m) (members : Array (KId m)) :
    RecM m Unit := do
  -- SECURITY INVARIANT (Lean #14576): infer each original stored member
  -- type, including every constructor type, before building or consulting
  -- any flattened/nested-inductive representation. A lossy nested rewrite
  -- can erase phantom parameter arguments; checking only that rewritten
  -- form would let an ill-typed argument disappear. Keep this pass in full
  -- inference mode and over the untouched `ty` values.
  let (indIds, ctorIds) ← classifyInductiveBlockMembers block members.toList
    #[] #[]
  checkInductiveMembers indIds.toList
  checkInductiveConstructorMembers ctorIds.toList

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

/-- Reuse or append the exact auxiliary specialization discovered by the
    flat-block scan.  Keeping this decision as a named production action
    exposes the shared specialization key to the E2c transport without
    changing the source-ordered queue traversal around it. -/
def appendNestedAuxiliary (headId : KId m)
    (occurrenceUs : Array (KUniv m)) (specParams : Array (KExpr m))
    (extParams extIndices : UInt64) (extCtors : Array (KId m))
    (extLvls : UInt64) (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64) :
    RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey) := do
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
  appendNestedAuxiliary headId occurrenceUs specParams extParams extIndices
    extCtors extLvls flat auxSeen univOffset

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

/-- Consume the declared parameter prefix of one flat-block constructor.
The explicit recursion is the source-ordered equivalent of the former range
loop and exposes its early non-forall stop to verification. -/
def instantiateFlatConstructorParams (member : FlatBlockMember m)
    (nRecParams : UInt64) : Nat → Nat → KExpr m → RecM m (KExpr m)
  | 0, _, cur => pure cur
  | remaining + 1, j, cur => do
      let w ← whnf cur
      match w with
      | .all _ _ _ body _ =>
        let p := if j < member.specParams.size then
            member.specParams[j]!
          else
            .mkVar (nRecParams - 1 - j.toUInt64) anonN
        let cur ← TcM.runIntern (subst body p 0)
        instantiateFlatConstructorParams member nRecParams remaining (j + 1)
          cur
      | _ => pure cur

/-- Scan one constructor's fields in source order, threading the dynamically
growing flat block and exact deduplication array. -/
def scanFlatConstructorFields (allBlockAddrs : Array Address)
    (nRecParams univOffset : UInt64) (paramDepth : Nat) :
    Nat → KExpr m →
      (Array (FlatBlockMember m) × Array NestedSpecializationKey) →
      RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey)
  | 0, _, pair => pure pair
  | remaining + 1, cur, pair => do
      let w ← whnf cur
      match w with
      | .all _ _ dom body _ =>
        let pair ← tryDetectNested dom allBlockAddrs pair.1 pair.2 univOffset
          paramDepth nRecParams
        let (open', _) ← TcM.openBinderAnon dom body
        scanFlatConstructorFields allBlockAddrs nRecParams univOffset
          paramDepth remaining open' pair
      | _ => pure pair

/-- Scan one source constructor, including universe instantiation, parameter
substitution, nested-field discovery, and the production lctx restoration. -/
def scanFlatConstructor (allBlockAddrs : Array Address)
    (nRecParams univOffset : UInt64) (member : FlatBlockMember m)
    (ctorId : KId m)
    (pair : Array (FlatBlockMember m) × Array NestedSpecializationKey) :
    RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey) := do
  let some (.ctor (fields := ctorFields) (ty := ctorTy) ..) ←
      TcM.tryGetConst ctorId
    | return pair
  let ctorTyInst ← TcM.instantiateUnivParams ctorTy member.occurrenceUs
  let saved := (← get).lctx.size
  let cur ← instantiateFlatConstructorParams member nRecParams
    member.ownParams.toNat 0 ctorTyInst
  let pair ← scanFlatConstructorFields allBlockAddrs nRecParams univOffset
    saved ctorFields.toNat cur pair
  modify fun s => { s with lctx := s.lctx.truncate saved }
  return pair

/-- Scan a constructor list in source order while retaining the pair returned
by every successful nested-field detection. -/
def scanFlatConstructors (allBlockAddrs : Array Address)
    (nRecParams univOffset : UInt64) (member : FlatBlockMember m) :
    List (KId m) →
      (Array (FlatBlockMember m) × Array NestedSpecializationKey) →
      RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey)
  | [], pair => pure pair
  | ctorId :: ctorIds, pair => do
      let pair ← scanFlatConstructor allBlockAddrs nRecParams univOffset
        member ctorId pair
      scanFlatConstructors allBlockAddrs nRecParams univOffset member ctorIds
        pair

/-- One source-ordered production queue step.  Naming the callback preserves
the executable traversal while exposing the dynamically growing flat array
and its deduplication set to E2c proofs. -/
def buildFlatBlockQueueStep (allBlockAddrs : Array Address)
    (nRecParams univOffset : UInt64) (state : FlatBlockQueueState m) :
    RecM m (BoundedStep (FlatBlockQueueState m)
      (Array (FlatBlockMember m) × Array NestedSpecializationKey)) := do
  let (qi, flat0, auxSeen0) := state
  if qi ≥ flat0.size then
    return .done (flat0, auxSeen0)
  let member := flat0[qi]!
  let pair ← scanFlatConstructors allBlockAddrs nRecParams univOffset member
    member.ctors.toList (flat0, auxSeen0)
  return .next (qi + 1, pair.1, pair.2)

/-- Exact de Bruijn parameter vector stored on each original flat-block
member. -/
def mkFlatBlockSpecParams (nRecParams : UInt64) : Array (KExpr m) :=
  (Array.range nRecParams.toNat).map fun j =>
    .mkVar (nRecParams - 1 - j.toUInt64) anonN

/-- Seed original block members in source order before nested auxiliaries are
discovered.  Naming this recursion exposes that every seeded member is
non-auxiliary while preserving the production lookup/intern sequence. -/
def seedFlatBlockMembers (nRecParams univOffset : UInt64) :
    List (KId m) → Array (FlatBlockMember m) →
      RecM m (Array (FlatBlockMember m))
  | [], flat => pure flat
  | indId :: indIds, flat => do
      let concrete ← TcM.getConst indId
      match concrete with
      | .indc (params := ownParams) (indices := nIndices) (ctors := ctors)
          (lvls := lvls) .. =>
        let indUs ← mkIndUnivs lvls univOffset
        let flat := flat.push
          { id := indId, isAux := false,
            specParams := mkFlatBlockSpecParams nRecParams,
            ownParams, nIndices, ctors, lvls, indUs, occurrenceUs := indUs }
        seedFlatBlockMembers nRecParams univOffset indIds flat
      | _ => seedFlatBlockMembers nRecParams univOffset indIds flat

/-- Build the flat block while retaining the exact auxiliary-deduplication set
for verification.  The public wrapper below projects the original result. -/
def buildFlatBlockWithAuxSeen (blockInds : Array (KId m))
    (nRecParams univOffset : UInt64) :
    RecM m (Array (FlatBlockMember m) × Array NestedSpecializationKey) := do
  let allBlockAddrs := blockInds.map (·.addr)
  let flat ← seedFlatBlockMembers nRecParams univOffset blockInds.toList #[]
  -- Queue-based scan (flat grows while iterating).
  runBounded (buildFlatBlockQueueStep allBlockAddrs nRecParams univOffset)
    maxWhnfFuel.toNat (0, flat, #[])

/-- Build the flat block: originals seeded, then a queue pass over every
member's constructor fields detecting nested occurrences. -/
def buildFlatBlock (blockInds : Array (KId m))
    (nRecParams univOffset : UInt64) :
    RecM m (Array (FlatBlockMember m)) := do
  return (← buildFlatBlockWithAuxSeen blockInds nRecParams univOffset).1

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

/-- Whether an expression already exposes one of the flattened inductive
    members at the head of its application spine.  Such a head is irreducible:
    WHNF cannot turn it into another forall or recursive target. -/
def hasFlatMemberHead (e : KExpr m) (flat : Array (FlatBlockMember m)) : Bool :=
  let (head, _) := e.collectSpine
  match head with
  | .const id _ _ => flat.any fun member => member.id.addr == id.addr
  | _ => false

/-- Recursive-field detection: after peeling foralls, `I_k params args`
    matching a flat member. Aux members additionally def-eq the first
    `ownParams` args against spec_params lifted by `specParamsLiftBy`. -/
def isRecField (dom : KExpr m) (flat : Array (FlatBlockMember m))
    (specParamsLiftBy : UInt64) : RecM m (Option Nat) := do
  runBounded (fun ty => do
    -- An exposed flat-member spine is already headed by an inductive
    -- constant, so full WHNF cannot reveal a different recursive target.
    -- Avoiding that redundant callback is also important for rule building:
    -- its final lambda positions are represented by loose de Bruijn variables
    -- which do not inhabit the checker's live local context.  Hidden heads
    -- and every non-member constant still take the ordinary WHNF path.
    let w ← if hasFlatMemberHead ty flat then pure ty else whnf ty
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

/-- Close the generated recursor's domain array from right to left while
restoring the local context.  The explicit recursion exposes every exact
intern request to the generated-artifact proof without changing the former
range-loop order. -/
def closeGeneratedRecursorForalls (saved : Nat)
    (domains : Array (KExpr m)) : Nat → KExpr m → RecM m (KExpr m)
  | 0, body => do
      modify fun s => { s with lctx := s.lctx.truncate saved }
      return body
  | remaining + 1, body => do
      modify fun s => { s with
        lctx := s.lctx.truncate (s.lctx.size - 1) }
      let body ← TcM.intern
        (.mkAll anonN anonBi domains[remaining]! body)
      closeGeneratedRecursorForalls saved domains remaining body

/-- Build the parameter, motive, minor, index, and major domains plus the
return body, leaving every domain open in the local context. -/
def buildGeneratedRecursorTypeBody (di : Nat)
    (indInfos : Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m)) (univOffset : UInt64) :
    RecM m (GeneratedRecursorTypeBody m) := do
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
  return { saved, domains, body := ret }

/-- Full recursor type for flat member `di`:
    `∀ params motives minors indices major, motive indices major`. -/
def buildRecType (di : Nat)
    (indInfos : Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m)) (univOffset : UInt64) :
    RecM m (KExpr m) := do
  let built ← buildGeneratedRecursorTypeBody di indInfos blockInds flat
    motiveTypes univOffset
  closeGeneratedRecursorForalls built.saved built.domains built.domains.size
    built.body

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
  -- Peel foralls (stop when the result head is a flat member).  Direct
  -- recursive domains are already in WHNF and may refer to the future rule
  -- lambda frame rather than the live checker context.
  let wdom ← if hasFlatMemberHead dom flat then pure dom else whnf dom
  let (forallDoms, inner) := peelRuleIhForalls wdom flat
  let nXs := forallDoms.size.toUInt64
  let innerW ← if hasFlatMemberHead inner flat then pure inner else whnf inner
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
    -- The constructor result is an exposed application of its flat member.
    -- It cannot reduce to another field forall, and in rule construction its
    -- arguments can contain virtual (not live-context) de Bruijn variables.
    if hasFlatMemberHead tmp flat then
      return .done nFields
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
    -- As in the counting pass, stop before sending the exposed inductive
    -- result (whose arguments are in the future lambda frame) through WHNF.
    if hasFlatMemberHead fieldTy flat then
      return .done (fieldTy, fieldIdx, loopBody)
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

/-- Initial cache entry for one exact flat-block member.  Rules are populated
    only after every peer recursor type has been constructed. -/
def initialGeneratedRecursor (member : FlatBlockMember m)
    (flat : Array (FlatBlockMember m)) (recLvls nParams nMinors : UInt64)
    (blockIsUnsafe : Bool) (recType : KExpr m) : GeneratedRecursor m :=
  { indAddr := member.id.addr
    lvls := recLvls
    params := nParams
    motives := flat.size.toUInt64
    minors := nMinors
    indices := member.nIndices
    isUnsafe := blockIsUnsafe
    ty := recType
    rules := #[] }

/-- Construct generated recursor types in flat-block order.  The explicit fuel
    is the number of members remaining; `generateBlockRecursors` starts at
    index zero with exactly `flat.size` steps.  Naming this existing loop makes
    its positional metadata contract available to the verification layer. -/
def buildGeneratedRecursorTypes
    (indInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m))
    (univOffset recLvls nParams nMinors : UInt64)
    (blockIsUnsafe : Bool) (di : Nat) :
    Nat → Array (GeneratedRecursor m) → RecM m (Array (GeneratedRecursor m))
  | 0, generated => pure generated
  | fuel + 1, generated => do
      if h : di < flat.size then
        let recType ← buildRecType di indInfos blockInds flat motiveTypes
          univOffset
        let generated := generated.push
          (initialGeneratedRecursor flat[di] flat recLvls nParams nMinors
            blockIsUnsafe recType)
        buildGeneratedRecursorTypes indInfos blockInds flat motiveTypes
          univOffset recLvls nParams nMinors blockIsUnsafe (di + 1) fuel
          generated
      else
        pure generated

/-- Attempt to construct every rule for one generated recursor.  Errors from
    an individual RHS are retained as `none`, matching the best-effort rule
    population performed before a co-resident recursor block is available. -/
def buildOptionalGeneratedRecursorRules (gi : Nat)
    (member : FlatBlockMember m) (flat : Array (FlatBlockMember m))
    (peers : Array (KId m)) (recTy : KExpr m) (nParams : Nat)
    (isLarge : Bool) : RecM m (Array (Option (RecRule m))) := do
  let mut rules : Array (Option (RecRule m)) := #[]
  for h : ci in [0:member.ctors.size] do
    let ctorId := member.ctors[ci]
    let ctorFields ← match (← TcM.getConst ctorId) with
      | .ctor (fields := fields) .. => pure fields
      | _ => throw (.other "generate_block_recursors: ctor not found")
    let rhs? ← try?
      (buildRuleRhs gi ci ctorId member flat peers recTy nParams isLarge)
    match rhs? with
    | some rhs => rules := rules.push (some ⟨ctorId.name, ctorFields, rhs⟩)
    | none => rules := rules.push none
  return rules

/-- Populate best-effort rules in generated-recursors order.  Rule synthesis
    is stateful, but the only array mutation is `GeneratedRecursor.withRules`,
    whose metadata projection is definitionally unchanged. -/
def populateOptionalGeneratedRecursorRules
    (flat : Array (FlatBlockMember m)) (peers : Array (KId m))
    (nParams : Nat) (isLarge : Bool) (gi : Nat) :
    Nat → Array (GeneratedRecursor m) → RecM m (Array (GeneratedRecursor m))
  | 0, generated => pure generated
  | fuel + 1, generated => do
      let member := flat[gi]!
      let rules ← buildOptionalGeneratedRecursorRules gi member flat peers
        generated[gi]!.ty nParams isLarge
      let generated := if rules.all (·.isSome) then
          generated.modify gi (·.withRules (rules.filterMap id))
        else generated
      populateOptionalGeneratedRecursorRules flat peers nParams isLarge
        (gi + 1) fuel generated

/-- Construct the complete rule array for one generated recursor after the
    checked recursor block has supplied canonically aligned peers. -/
def buildCompleteGeneratedRecursorRules (gi : Nat)
    (member : FlatBlockMember m) (flat : Array (FlatBlockMember m))
    (peers : Array (KId m)) (recTy : KExpr m) (nParams : Nat)
    (isLarge : Bool) : RecM m (Array (RecRule m)) := do
  let mut rules : Array (RecRule m) := Array.mkEmpty member.ctors.size
  for h : ci in [0:member.ctors.size] do
    let ctorId := member.ctors[ci]
    let ctorFields ← match (← TcM.getConst ctorId) with
      | .ctor (fields := fields) .. => pure fields
      | _ => throw (.other "populate_recursor_rules_from_block: ctor not found")
    let rhs ← buildRuleRhs gi ci ctorId member flat peers recTy nParams
      isLarge
    rules := rules.push ⟨ctorId.name, ctorFields, rhs⟩
  return rules

/-- Populate complete rules in flat-block order after canonical peer
    alignment. -/
def populateCompleteGeneratedRecursorRules
    (flat : Array (FlatBlockMember m)) (peers : Array (KId m))
    (nParams : Nat) (isLarge : Bool) (gi : Nat) :
    Nat → Array (GeneratedRecursor m) → RecM m (Array (GeneratedRecursor m))
  | 0, generated => pure generated
  | fuel + 1, generated => do
      let member := flat[gi]!
      let rules ← buildCompleteGeneratedRecursorRules gi member flat peers
        generated[gi]!.ty nParams isLarge
      let generated := generated.modify gi (·.withRules rules)
      populateCompleteGeneratedRecursorRules flat peers nParams isLarge
        (gi + 1) fuel generated

/-- Transactionally install a locally produced rule batch. The target cache
    must still contain the ingress batch's exact positional metadata, but its
    current types and rules are deliberately ignored: stateful callbacks may
    have replaced either while constructing rules. Every installed header and
    type comes from the immutable ingress snapshot; only rule arrays come from
    `generatedWithRules`. -/
def commitGeneratedRecursorRulesAt (indBlockId : KId m)
    (expected generatedWithRules : Array (GeneratedRecursor m)) :
    RecM m Unit := do
  let some cached := (← get).env.recursorCache[indBlockId]?
    | throw (.other
        "populate_recursor_rules_from_block: cache disappeared during rule construction")
  if cached.size != expected.size then
    throw (.other s!"populate_recursor_rules_from_block: cache changed length: cached={cached.size} expected={expected.size}")
  if cached.map GeneratedRecursor.metadata ==
      expected.map GeneratedRecursor.metadata then
    pure ()
  else
    throw (.other
      "populate_recursor_rules_from_block: cache header metadata changed during rule construction")
  if generatedWithRules.size != expected.size then
    throw (.other s!"populate_recursor_rules_from_block: generated rule batch changed length: generated={generatedWithRules.size} expected={expected.size}")
  let installed := expected.zipWith
    (fun header generated => header.withRules generated.rules)
    generatedWithRules
  modify fun s => { s with env := { s.env with
    recursorCache := s.env.recursorCache.insert indBlockId installed } }

/-- Build every generated recursor, opportunistically populate co-resident
    rules, and insert the resulting batch into both recursor caches.  All
    inputs have already been checked and the flat block has already been
    canonicalized by `generateBlockRecursors`. -/
def buildAndCacheGeneratedRecursors (blockId : KId m)
    (flatIndInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (flatIds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m))
    (univOffset recLvls nParams nMinors : UInt64)
    (blockIsUnsafe isLarge : Bool) : RecM m Unit := do
  let generated ← buildGeneratedRecursorTypes flatIndInfos flatIds flat
    motiveTypes univOffset recLvls nParams nMinors blockIsUnsafe 0 flat.size
      (Array.mkEmpty flat.size)
  let peerRecs ← findPeerRecursors blockId flat
  let generated ← match peerRecs with
    | some peers =>
      populateOptionalGeneratedRecursorRules flat peers nParams.toNat isLarge
        0 generated.size generated
    | none => pure generated
  let majorsKey := sortedDedupIds flatIds
  modify fun s => { s with env := { s.env with
    recMajorsCache := s.env.recMajorsCache.insert majorsKey blockId,
    recursorCache := s.env.recursorCache.insert blockId generated } }

/-- Discover, validate, flatten, and build motives for one block using the
exact production preparation path. `none` is the valid empty-block result;
errors remain hard failures. -/
def prepareGeneratedRecursorBuildInputs (blockId : KId m) :
    RecM m (Option (GeneratedRecursorBuildInputs m)) := do
  let blockInds ← discoverBlockInductives blockId
  if blockInds.isEmpty then
    return none
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
  let nMinors ← checkedMetadataSum "generated recursor minors"
    (flat.map fun mem => mem.ctors.size.toUInt64)
  return some {
    flatIndInfos
    flatIds
    flat
    motiveTypes
    univOffset
    recLvls
    nParams
    nMinors
    blockIsUnsafe
    isLarge }

/-- Generate recursors for every flat member of an inductive block and
    cache them (`recursorCache`, `recMajorsCache`). -/
def generateBlockRecursors (blockId : KId m) : RecM m Unit := do
  let some inputs ← prepareGeneratedRecursorBuildInputs blockId | do
    modify fun s => { s with env := { s.env with
      recursorCache := s.env.recursorCache.insert blockId #[] } }
    return ()
  buildAndCacheGeneratedRecursors blockId inputs.flatIndInfos inputs.flatIds
    inputs.flat inputs.motiveTypes inputs.univOffset inputs.recLvls
    inputs.nParams inputs.nMinors inputs.blockIsUnsafe inputs.isLarge

/-- Internal rule-population body for one already-snapshotted generated batch.
Every early path returns the immutable ingress batch. The complete path
returns a locally built batch whose only changes are canonical rule arrays;
neither path commits callback-mutated cache contents. -/
def populateRecursorRulesFromBlockCore (indBlockId recBlockId : KId m)
    (generatedSnapshot : Array (GeneratedRecursor m)) :
    RecM m (Array (GeneratedRecursor m)) := do
  if generatedSnapshot.isEmpty then
    return generatedSnapshot
  let some members ← TcM.tryGetBlock recBlockId
    | return generatedSnapshot
  let mut recIds : Array (KId m) := #[]
  for id in members do
    if let some (.recr ..) ← TcM.tryGetConst id then
      recIds := recIds.push id
  if recIds.isEmpty then
    return generatedSnapshot
  let blockInds ← discoverBlockInductives indBlockId
  if blockInds.isEmpty then
    return generatedSnapshot
  let nParams64 ← match (← TcM.tryGetConst blockInds[0]!) with
    | some (.indc (params := params) ..) => pure params
    | _ => return generatedSnapshot
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
    return generatedSnapshot
  if recIds.size != flat.size then
    throw (.other s!"populate_recursor_rules_from_block: rec_ids/flat count mismatch: rec_ids={recIds.size} flat={flat.size}")
  -- Verify canonical alignment on complete closed types and every stored
  -- header field. Peeling forall bodies here would expose dangling de Bruijn
  -- variables to stateful WHNF/DefEq callbacks.
  let mut peers : Array (KId m) := Array.mkEmpty flat.size
  for h : gi in [0:generatedSnapshot.size] do
    let genRec := generatedSnapshot[gi]
    let rid := recIds[gi]!
    let (lvls, isUnsafe, params, motives, minors, indices, ty) ←
      match (← TcM.getConst rid) with
      | .recr (lvls := lvls) (isUnsafe := isUnsafe) (params := p)
          (motives := mo) (minors := mi) (indices := ix) (ty := ty) .. =>
        pure (lvls, isUnsafe, p, mo, mi, ix, ty)
      | _ => throw (.other s!"populate_recursor_rules_from_block: rec_ids[{gi}]={rid} is not a recursor")
    if lvls != genRec.lvls || isUnsafe != genRec.isUnsafe ||
        params != genRec.params || motives != genRec.motives ||
        minors != genRec.minors || indices != genRec.indices then
      throw (.other s!"populate_recursor_rules_from_block: canonical header mismatch at peer {gi}")
    if !(← isDefEq genRec.ty ty) then
      throw (.other s!"populate_recursor_rules_from_block: canonical-order mismatch at peer {gi}")
    peers := peers.push rid
  let isLarge := univOffset > 0
  populateCompleteGeneratedRecursorRules flat peers nParams64.toNat isLarge 0
    flat.size generatedSnapshot

/-- Populate canonical rules from the recursor block's peers (block-level
    recursor checking path). Verifies canonical alignment peer-by-peer via
complete closed types and header metadata; a divergence is a hard error. Every successful run
with an ingress cache entry transactionally restores its exact headers and
types, including early returns after stateful lazy lookup, and installs only
rules returned by the local construction path. -/
def populateRecursorRulesFromBlock (indBlockId recBlockId : KId m) :
    RecM m Unit := do
  let some generatedSnapshot := (← get).env.recursorCache[indBlockId]?
    | return ()
  let generatedWithRules ←
    populateRecursorRulesFromBlockCore indBlockId recBlockId generatedSnapshot
  commitGeneratedRecursorRulesAt indBlockId generatedSnapshot
    generatedWithRules

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

/-- Check, in source order, that every physical block member is an inductive
    declaration or one of its constructors.  The recursive seam is
    operationally identical to the corresponding early-exit loop in Rust,
    including lazy-ingress errors and the first unsupported-member stop. -/
def inductiveBlockMembersAreSupported : List (KId m) → RecM m Bool
  | [] => pure true
  | member :: members => do
      match (← TcM.tryGetConst member) with
      | some (.indc ..) | some (.ctor ..) =>
          inductiveBlockMembersAreSupported members
      | _ => pure false

/-- Block-coordinated inductive validation (inductive.rs `check_inductive`):
    pure inductive blocks route through `blockCheckResults`; anything else
    falls back to the member check. -/
def checkInductive (id : KId m) : RecM m Unit := do
  let block ← match (← TcM.getConst id) with
    | .indc (block := block) .. => pure block
    | _ => throw (.other "check_inductive: not an inductive")
  let some members ← TcM.tryGetBlock block
    | return (← checkInductiveMemberImpl id)
  if !(← inductiveBlockMembersAreSupported members.toList) then
    return (← checkInductiveMemberImpl id)
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

/-- Compare every generated rule against the same-index rule from the frozen
stored declaration. `fuel` is the remaining suffix length; callers establish
the array-size equality before entering this loop. -/
def checkGeneratedRecursorRules (generatedRules storedRules :
    Array (RecRule m)) (index : Nat) : Nat → RecM m Unit
  | 0 => pure ()
  | fuel + 1 => do
      let generatedRule := generatedRules[index]!
      let storedRule := storedRules[index]!
      if generatedRule.fields != storedRule.fields then
        throw (.other s!"check_recursor: rule {index} field count mismatch: gen={generatedRule.fields} stored={storedRule.fields}")
      if !(← isDefEq generatedRule.rhs storedRule.rhs) then
        throw (.other s!"check_recursor: rule {index} RHS mismatch")
      checkGeneratedRecursorRules generatedRules storedRules (index + 1) fuel

/-- Exhaustively compare one selected generated entry with the complete
stored recursor snapshot: all header arities, the type, the rule count, every
field count, and every rule RHS. -/
def checkGeneratedRecursorCandidate (ty : KExpr m)
    (declaredLvls : UInt64) (declaredIsUnsafe : Bool)
    (params motives minors indices : UInt64)
    (storedRules : Array (RecRule m))
    (generated : GeneratedRecursor m) : RecM m Unit := do
  if declaredLvls != generated.lvls then
    throw (.other s!"check_recursor: universe arity mismatch: stored={declaredLvls}, generated={generated.lvls}")
  if declaredIsUnsafe != generated.isUnsafe then
    throw (.other s!"check_recursor: safety mismatch: stored={declaredIsUnsafe}, generated={generated.isUnsafe}")
  if params != generated.params || motives != generated.motives
      || minors != generated.minors || indices != generated.indices then
    throw (.other s!"check_recursor: arity metadata mismatch: stored=(params={params}, motives={motives}, minors={minors}, indices={indices}), generated=(params={generated.params}, motives={generated.motives}, minors={generated.minors}, indices={generated.indices})")
  if !(← isDefEq generated.ty ty) then
    throw (.other "check_recursor: type mismatch")
  let generatedRules := generated.rules
  if generatedRules.isEmpty && !storedRules.isEmpty then
    -- C1: cannot verify stored rules against a missing canonical form.
    throw (.other s!"check_recursor: rule generation failed, cannot verify {storedRules.size} stored rules")
  else if !generatedRules.isEmpty && storedRules.isEmpty then
    throw (.other s!"check_recursor: stored recursor has no rules (expected {generatedRules.size})")
  else if generatedRules.size != storedRules.size then
    throw (.other s!"check_recursor: rule count mismatch: gen={generatedRules.size} stored={storedRules.size}")
  checkGeneratedRecursorRules generatedRules storedRules 0
    generatedRules.size

/-- One auditable full-type selection iteration.  Totalized array lookup makes
the helper independently reusable by verification; production supplies
exactly `List.range generated.size`. -/
def generatedRecursorSelectionStep (ty : KExpr m)
    (params motives minors : UInt64) (indId : KId m)
    (generated : Array (GeneratedRecursor m)) (typeMatches : Array Nat)
    (gi : Nat) : RecM m (Array Nat) := do
  let some g := generated[gi]?
    | return typeMatches
  if g.indAddr != indId.addr || g.params != params ||
      g.motives != motives || g.minors != minors then
    return typeMatches
  if ← isDefEq g.ty ty then
    return typeMatches.push gi
  return typeMatches

/-- Compare the generated entry at the canonical stored block position with
the frozen stored type.  A successful result is still justified by a complete
closed-type comparison; the position only determines which candidate to try
first. -/
def selectGeneratedRecursorAtPosition (storedPos : Option Nat)
    (ty : KExpr m) (params motives minors : UInt64) (indId : KId m)
    (generated : Array (GeneratedRecursor m)) : RecM m (Option Nat) := do
  let some index := storedPos
    | return none
  let some selected := generated[index]?
    | return none
  if selected.indAddr != indId.addr || selected.params != params ||
      selected.motives != motives || selected.minors != minors then
    return none
  if ← isDefEq selected.ty ty then
    return some index
  return none

/-- Collect every remaining metadata-compatible generated entry whose complete
closed type is definitionally equal to the frozen stored type.  The explicit
list fold exposes the precise fallback callback order to verification. -/
def collectGeneratedRecursorTypeMatches (ty : KExpr m)
    (params motives minors : UInt64) (indId : KId m)
    (generated : Array (GeneratedRecursor m))
    (skip : Option Nat) : RecM m (Array Nat) :=
  ((List.range generated.size).filter fun index => some index != skip).foldlM
    (generatedRecursorSelectionStep ty params motives minors indId generated)
    #[]

/-- Select the generated recursor corresponding to one frozen stored
declaration. Complete recursor types are closed, unlike major domains peeled
from under forall binders, so the stateful DefEq calls remain inside the
top-level K2 translation context. Returning the index separately gives
verification an exact boundary between selection and exhaustive comparison. -/
def selectGeneratedRecursorIndex (recBlock id : KId m) (ty : KExpr m)
    (params motives minors : UInt64) (indId : KId m)
    (generated : Array (GeneratedRecursor m)) : RecM m (Option Nat) := do
  -- Full-type selection disambiguates auxiliaries sharing a major head.  The
  -- canonical block position is already established by the surrounding block
  -- checks, so try it first without weakening the complete-type comparison.
  let storedPos := (← get).env.blocks[recBlock]?.bind
    (·.findIdx? (fun mem => mem == id))
  match ← selectGeneratedRecursorAtPosition storedPos ty params motives
      minors indId generated with
  | some selected => return some selected
  | none =>
    let typeMatches ← collectGeneratedRecursorTypeMatches ty params motives
      minors indId generated storedPos
    return typeMatches[0]?

/-- Select from one frozen generated cache snapshot and exhaustively compare
the selected entry with the complete frozen stored declaration. -/
def checkGeneratedRecursorFromCache (recBlock id : KId m) (ty : KExpr m)
    (declaredLvls : UInt64) (declaredIsUnsafe : Bool)
    (params motives minors indices : UInt64) (indId : KId m)
    (storedRules : Array (RecRule m))
    (generated : Array (GeneratedRecursor m)) : RecM m Unit := do
  let selectedIdx ← selectGeneratedRecursorIndex recBlock id ty params
    motives minors indId generated
  match selectedIdx.bind (generated[·]?) with
  | some selected =>
    checkGeneratedRecursorCandidate ty declaredLvls declaredIsUnsafe params
      motives minors indices storedRules selected
  | none =>
    -- C2: no generated recursor — MUST NOT silently pass.
    throw (.other "check_recursor: no generated recursor for major")

/-- Freeze the complete stored recursor declaration and validate the exact
metadata sum used to locate its major argument.  This stage has no recursive
method callback. -/
def snapshotRecursorMemberDeclaration (id : KId m) :
    RecM m (RecursorMemberDeclarationSnapshot m) := do
  let (recBlock, ty, declaredK, declaredLvls, declaredIsUnsafe, params,
      motives, minors, indices, storedRules) ←
    match (← TcM.getConst id) with
    | .recr (block := block) (ty := ty) (k := k) (params := p)
        (lvls := lvls) (isUnsafe := isUnsafe) (motives := mo)
        (minors := mi) (indices := ix) (rules := rules) .. =>
      pure (block, ty, k, lvls, isUnsafe, p, mo, mi, ix, rules)
    | _ => throw (.other "check_recursor: not a recursor")
  let majorSkip ← checkedMetadataSum "recursor major index"
    #[params, motives, minors, indices]
  return {
    recBlock
    ty
    declaredK
    declaredLvls
    declaredIsUnsafe
    params
    motives
    minors
    indices
    storedRules
    majorSkip
  }

/-- Discover the stored recursor's major owner and replay the inductive
coherence gate before any generated-cache lookup is trusted. -/
def validateRecursorMemberMajor
    (snapshot : RecursorMemberDeclarationSnapshot m) : RecM m (KId m) := do
  let indId ← getMajorInductiveId snapshot.ty snapshot.majorSkip
  if let some (.indc ..) ← TcM.tryGetConst indId then
    checkInductive indId
  return indId

/-- Read-only fast-path query for an already generated block belonging to the
validated major.  Naming the query keeps its lazy lookup effects separate
from the peer-major generation fallback. -/
def findUsableGeneratedRecursorBlock
    (snapshot : RecursorMemberDeclarationSnapshot m) (indId : KId m) :
    RecM m (Option (KId m)) := do
  let indBlock ← match (← TcM.tryGetConst indId) with
    | some (.indc (block := block) ..) => pure (some block)
    | _ => pure none
  match indBlock with
    | some ib =>
      match (← get).env.recursorCache[ib]? with
      | some cached =>
        if cached.size.toUInt64 ≥ snapshot.motives then
          pure (some ib)
        else
          pure none
      | none => pure none
    | none => pure none

/-- Resolve the generated-recursor cache block for the validated major.  The
fast path consumes an already large-enough cache entry; the fallback preserves
production's peer-major lookup and on-demand block generation exactly. -/
def resolveRecursorMemberBlock
    (snapshot : RecursorMemberDeclarationSnapshot m) (indId : KId m) :
    RecM m (KId m) := do
  let resolvedBlock? ← findUsableGeneratedRecursorBlock snapshot indId
  match resolvedBlock? with
  | some block => pure block
  | none =>
    let majorsKey ← gatherPeerMajors snapshot.recBlock
    match (← get).env.recMajorsCache[majorsKey]? with
    | some blockId => pure blockId
    | none =>
      for majorId in majorsKey do
        if let some (.indc (block := block) ..) ← TcM.tryGetConst majorId then
          if !(← get).env.recursorCache.contains block then
            let _ ← try? (generateBlockRecursors block)
      let majorsKey2 ← gatherPeerMajors snapshot.recBlock
      match (← get).env.recMajorsCache[majorsKey2]? with
      | some blockId => pure blockId
      | none =>
        throw (.other
          "check_recursor: could not resolve inductive block")

/-- Compute and validate the constructive K flag for the already validated
major.  Returning the computed bit retains the exact value passed to the
checker handoff. -/
def validateRecursorMemberKTarget
    (snapshot : RecursorMemberDeclarationSnapshot m) (indId : KId m) :
    RecM m Bool := do
  let computedK ← computeKTarget indId
  if snapshot.declaredK != computedK then
    throw (.other s!"check_recursor: K-target mismatch: declared k={snapshot.declaredK}, computed k={computedK}")
  return computedK

/-- Freeze the generated batch only after transactional rule population has
completed.  A missing target is a hard failure; the comparison tail never
observes a live cache lookup. -/
def snapshotGeneratedRecursors (resolvedBlock : KId m) :
    RecM m (Array (GeneratedRecursor m)) := do
  let some generated := (← get).env.recursorCache[resolvedBlock]?
    | throw (.other "check_recursor: no generated recursors")
  return generated

/-- Run the stateful recursor-member prelude and return the exact frozen inputs
to the final generated-artifact checker.  Successful preparation has already
validated the major owner, inductive coherence, block resolution, the
constructive K target, and the transactional generated-rule population. -/
def prepareRecursorMemberCheck (id : KId m) :
    RecM m (PreparedRecursorMemberCheck m) := do
  let snapshot ← snapshotRecursorMemberDeclaration id
  let indId ← validateRecursorMemberMajor snapshot
  let resolvedBlock ← resolveRecursorMemberBlock snapshot indId
  let computedK ← validateRecursorMemberKTarget snapshot indId
  populateRecursorRulesFromBlock resolvedBlock snapshot.recBlock
  let generated ← snapshotGeneratedRecursors resolvedBlock
  return {
    recBlock := snapshot.recBlock
    ty := snapshot.ty
    declaredK := snapshot.declaredK
    declaredLvls := snapshot.declaredLvls
    declaredIsUnsafe := snapshot.declaredIsUnsafe
    params := snapshot.params
    motives := snapshot.motives
    minors := snapshot.minors
    indices := snapshot.indices
    storedRules := snapshot.storedRules
    indId
    resolvedBlock
    computedK
    generated
  }

/-- Consume one frozen preparation result through the exhaustive generated
candidate checker.  This is deliberately a separate operation so verification
can state the exact handoff between the stateful prelude and comparison tail. -/
def checkPreparedRecursorMember (id : KId m)
    (prepared : PreparedRecursorMemberCheck m) : RecM m Unit :=
  checkGeneratedRecursorFromCache prepared.recBlock id prepared.ty
    prepared.declaredLvls prepared.declaredIsUnsafe prepared.params
    prepared.motives prepared.minors prepared.indices prepared.indId
    prepared.storedRules prepared.generated

/-- Validate a recursor against the generated canonical form (type def-eq +
    per-rule field count and RHS def-eq), with full-type aux
    disambiguation. Every successful path compares both type and rules. The
    complete stored declaration is snapshotted before any stateful comparison,
    so a callback cannot replace the rule array between type and rule checks. -/
def checkRecursorMemberImpl (id : KId m) : RecM m Unit := do
  let prepared ← prepareRecursorMemberCheck id
  checkPreparedRecursorMember id prepared

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
