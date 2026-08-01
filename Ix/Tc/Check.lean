module

public import Ix.Tc.Inductive

/-!
Mirror: crates/kernel/src/check.rs

Constant checking dispatch:
- `checkConst` clears per-constant state, then either routes through
  whole-block coordination (`blockCheckResults` memoizes `Except (TcError m)
  Unit`, so failures replay identically for every member) or checks the
  single member.
- Per-member checking: duplicate-level-param guard, well-scopedness
  validation (closed at top level, univ params in range, const arities,
  known prj heads), then kind dispatch — axioms/quots infer+sort;
  definitions additionally def-eq the value type (theorems must be Prop) and
  run the safety lattice; inductives/ctors/recursors run inference plus the
  inductive machinery.

The inductive and recursor member/block validators live in
`Ix.Tc.Inductive`.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashSet)

inductive CheckBlockKind where
  | defn
  | inductive'
  | recursor
  deriving BEq, Repr, Inhabited

/-- State update performed when a coordinated check publishes its captured
verdict.  All fields except `env.blockCheckResults` are preserved exactly. -/
def TcState.withBlockCheckResult (state : TcState m) (block : KId m)
    (result : Except (TcError m) Unit) : TcState m :=
  { state with env := { state.env with blockCheckResults :=
      state.env.blockCheckResults.insert block result } }

namespace RecM

-- ### Safety lattice

/-- Safe defs must not reference unsafe/partial constants; partial defs must
    not reference unsafe ones. Iterative walk, memoized. -/
def checkNoUnsafeRefs (root : KExpr m)
    (callerSafety : Ix.DefinitionSafety) : RecM m Unit :=
  go [root] {} {}
where
  /-- LIFO order matches the former Array stack. -/
  go (stack : List (KExpr m)) (seenExprs seenConsts : HashSet Address) :
      RecM m Unit :=
    match stack with
    | [] => pure ()
    | e :: stack => do
      if seenExprs.contains e.addr then
        return (← go stack seenExprs seenConsts)
      let seenExprs := seenExprs.insert e.addr
      match e with
      | .var .. | .fvar .. | .sort .. | .nat .. | .str .. =>
        go stack seenExprs seenConsts
      | .const id _ _ =>
        if seenConsts.contains id.addr then
          return (← go stack seenExprs seenConsts)
        let seenConsts := seenConsts.insert id.addr
        let short := (toString id.addr).take 8 |>.toString
        match (← TcM.tryGetConst id) with
        | some (.axio (isUnsafe := true) ..) =>
          throw (.other s!"safe definition references unsafe axiom {short}")
        | some (.defn (safety := .unsaf) ..) =>
          throw (.other s!"safe definition references unsafe definition {short}")
        | some (.defn (safety := .part) ..) =>
          if callerSafety == .safe then
            throw (.other s!"safe definition references partial definition {short}")
        | some (.recr (isUnsafe := true) ..) =>
          throw (.other s!"safe definition references unsafe recursor {short}")
        | some (.indc (isUnsafe := true) ..) =>
          throw (.other s!"safe definition references unsafe inductive {short}")
        | some (.ctor (isUnsafe := true) ..) =>
          throw (.other s!"safe definition references unsafe constructor {short}")
        | _ => pure ()
        go stack seenExprs seenConsts
      | .app f a _ => go (a :: f :: stack) seenExprs seenConsts
      | .lam _ _ ty body _ | .all _ _ ty body _ =>
        go (body :: ty :: stack) seenExprs seenConsts
      | .letE _ ty val body _ _ =>
        go (body :: val :: ty :: stack) seenExprs seenConsts
      | .prj _ _ val _ => go (val :: stack) seenExprs seenConsts
  termination_by exprWorkSize stack
  decreasing_by
    all_goals simp [exprWorkSize, KExpr.treeSize, KExpr.treeSize_pos] <;> omega

-- ### Quotient validation

/-- Count leading foralls (whnf-peeled, opened with fresh fvars). -/
def countForalls (ty : KExpr m) : RecM m Nat := do
  let saved := (← get).lctx.size
  runBounded (fun (cur, n) => do
    let w ← whnf cur
    match w with
    | .all name bi dom body _ =>
      let fvId ← TcM.freshFVarId (m := m)
      let fv ← TcM.intern (.mkFVar fvId name)
      modify fun s => { s with lctx := s.lctx.push fvId (.cdecl name bi dom) }
      let cur ← TcM.runIntern (instantiateRev body #[fv])
      return .next (cur, n + 1)
    | _ =>
      modify fun s => { s with lctx := s.lctx.truncate saved }
      return .done n) maxWhnfFuel.toNat (ty, 0)

/-- Implicit binder metadata for canonical primitive types. Binder metadata is
    hash-neutral in `KExpr`; retaining Lean's source binder info here makes the
    builder readable and keeps meta-mode egress faithful. -/
@[inline] def quotImplicitBi : {m : Mode} → m.F Lean.BinderInfo :=
  Mode.fieldWith fun _ => .implicit

@[inline] def canonicalVar (idx : UInt64) : KExpr m :=
  .mkVar idx anonN

@[inline] def canonicalAll (bi : m.F Lean.BinderInfo)
    (dom body : KExpr m) : KExpr m :=
  .mkAll anonN bi dom body

@[inline] def canonicalArrow (dom body : KExpr m) : KExpr m :=
  canonicalAll anonBi dom body

/-- `α → α → Prop` at a point where `α` is `Var(0)`. -/
def canonicalQuotRelation : KExpr m :=
  canonicalArrow (canonicalVar 0)
    (canonicalArrow (canonicalVar 1) (.mkSort .mkZero))

/-- Exact semantic type required of the `Eq` prerequisite used by
    `Environment.addQuot`. -/
def canonicalEqType : KExpr m :=
  let u : KUniv m := .mkParam 0 anonN
  canonicalAll quotImplicitBi (.mkSort u)
    (canonicalAll anonBi (canonicalVar 0)
      (canonicalAll anonBi (canonicalVar 1) (.mkSort .mkZero)))

/-- Exact semantic type required of the `Eq.refl` prerequisite used by
    `Environment.addQuot`. -/
def canonicalEqReflType (p : Primitives m) : KExpr m :=
  let u : KUniv m := .mkParam 0 anonN
  let result := KExpr.mkAppN (.mkConst p.eq #[u])
    #[canonicalVar 1, canonicalVar 0, canonicalVar 0]
  canonicalAll quotImplicitBi (.mkSort u)
    (canonicalAll anonBi (canonicalVar 0) result)

/-- Canonical type installed by Lean's `Environment.addQuot` for each
    reserved quotient primitive. Names and binder info are metadata; the
    de Bruijn structure, universes, primitive heads, and domains form the
    semantic acceptance contract. -/
def canonicalQuotType (p : Primitives m) (kind : Ix.QuotKind) : KExpr m :=
  let u : KUniv m := .mkParam 0 anonN
  let v : KUniv m := .mkParam 1 anonN
  let sortU : KExpr m := .mkSort u
  let prop : KExpr m := .mkSort .mkZero
  match kind with
  | .type =>
      canonicalAll quotImplicitBi sortU
        (canonicalAll anonBi canonicalQuotRelation sortU)
  | .ctor =>
      let result := KExpr.mkAppN (.mkConst p.quotType #[u])
        #[canonicalVar 2, canonicalVar 1]
      canonicalAll quotImplicitBi sortU
        (canonicalAll anonBi canonicalQuotRelation
          (canonicalAll anonBi (canonicalVar 1) result))
  | .lift =>
      let fTy := canonicalArrow (canonicalVar 2) (canonicalVar 1)
      let rab := KExpr.mkAppN (canonicalVar 4)
        #[canonicalVar 1, canonicalVar 0]
      let fa := KExpr.mkApp (canonicalVar 3) (canonicalVar 2)
      let fb := KExpr.mkApp (canonicalVar 3) (canonicalVar 1)
      let faEqFb := KExpr.mkAppN (.mkConst p.eq #[v])
        #[canonicalVar 4, fa, fb]
      let hTy := canonicalAll anonBi (canonicalVar 3)
        (canonicalAll anonBi (canonicalVar 4)
          (canonicalArrow rab faEqFb))
      let quotR := KExpr.mkAppN (.mkConst p.quotType #[u])
        #[canonicalVar 4, canonicalVar 3]
      canonicalAll quotImplicitBi sortU
        (canonicalAll quotImplicitBi canonicalQuotRelation
          (canonicalAll quotImplicitBi (.mkSort v)
            (canonicalAll anonBi fTy
              (canonicalAll anonBi hTy
                (canonicalArrow quotR (canonicalVar 3))))))
  | .ind =>
      let quotRD2 := KExpr.mkAppN (.mkConst p.quotType #[u])
        #[canonicalVar 1, canonicalVar 0]
      let betaTy := canonicalArrow quotRD2 prop
      let quotMkA := KExpr.mkAppN (.mkConst p.quotCtor #[u])
        #[canonicalVar 3, canonicalVar 2, canonicalVar 0]
      let mkMinor := canonicalAll anonBi (canonicalVar 2)
        (KExpr.mkApp (canonicalVar 1) quotMkA)
      let quotRD4 := KExpr.mkAppN (.mkConst p.quotType #[u])
        #[canonicalVar 3, canonicalVar 2]
      let result := KExpr.mkApp (canonicalVar 2) (canonicalVar 0)
      canonicalAll quotImplicitBi sortU
        (canonicalAll quotImplicitBi canonicalQuotRelation
          (canonicalAll quotImplicitBi betaTy
            (canonicalAll anonBi mkMinor
              (canonicalAll quotImplicitBi quotRD4 result))))

/-! ### Block classification data -/

/-- Accumulator used while production classifies one complete physical block.
Keeping it named exposes the homogeneous-kind check to verification without
changing the order or error behavior of member lookups. -/
structure BlockClassFlags where
  sawDefn : Bool := false
  sawRecr : Bool := false
  sawInductiveLike : Bool := false
  deriving Repr, Inhabited

namespace BlockClassFlags

/-- The initial empty shape census. -/
def empty : BlockClassFlags := ⟨false, false, false⟩

/-- Record the declaration shape of one loaded member, or reject a shape
which is intentionally outside coordinated checking. -/
def note (flags : BlockClassFlags) (member : KId m) (c : KConst m) :
    Except (TcError m) BlockClassFlags :=
  match c with
  | .defn .. => .ok { flags with sawDefn := true }
  | .recr .. => .ok { flags with sawRecr := true }
  | .indc .. | .ctor .. => .ok { flags with sawInductiveLike := true }
  | .axio .. | .quot .. =>
      .error (.other s!"unsupported check block {member}: axiom/quotient member")

/-- Convert the complete shape census to the one supported homogeneous
checker branch. -/
def finish (flags : BlockClassFlags) : Except (TcError m) CheckBlockKind :=
  match flags.sawDefn, flags.sawInductiveLike, flags.sawRecr with
  | true, false, false => .ok .defn
  | false, true, false => .ok .inductive'
  | false, false, true => .ok .recursor
  | _, _, _ =>
      .error (.other "unsupported mixed check block: expected only definitions, only inductives/constructors, or only recursors")

end BlockClassFlags

mutual

/-- `Eq` and `Eq.refl` must have the exact metadata and semantic types checked
    by Lean before it installs the quotient primitives. -/
def checkEqType : RecM m Unit := do
  let p ← prims
  let eqC? := (← get).env.consts.fold (init := none)
    fun acc id c => if id.addr == p.eq.addr then some (id, c) else acc
  let some (_, eqC) := eqC?
    | throw (.other "check_eq_type: Eq not found in environment")
  match eqC with
  | .indc (lvls := lvls) (params := params) (indices := indices)
      (isUnsafe := isUnsafe) (ty := ty) (ctors := ctors) .. =>
    if lvls != 1 then
      throw (.other s!"check_eq_type: Eq expects 1 universe param, got {lvls}")
    if params != 2 then
      throw (.other s!"check_eq_type: Eq expects 2 params (α, a), got {params}")
    if indices != 1 then
      throw (.other s!"check_eq_type: Eq expects 1 index, got {indices}")
    if isUnsafe then
      throw (.other "check_eq_type: Eq must be safe")
    if ctors.size != 1 then
      throw (.other s!"check_eq_type: Eq expects 1 constructor, got {ctors.size}")
    if ctors[0]!.addr != p.eqRefl.addr then
      throw (.other "check_eq_type: Eq's constructor is not Eq.refl")
    if ty.addr != (canonicalEqType (m := m)).addr then
      throw (.other "check_eq_type: Eq type is not canonical")
  | _ => throw (.other "check_eq_type: Eq not found or not inductive")
  let reflC? := (← get).env.consts.fold (init := none)
    fun acc id c => if id.addr == p.eqRefl.addr then some c else acc
  let some reflC := reflC?
    | throw (.other "check_eq_type: Eq.refl not found")
  match reflC with
  | .ctor (isUnsafe := isUnsafe) (lvls := lvls) (induct := induct)
      (cidx := cidx) (params := params) (fields := fields) (ty := ty) .. =>
    if isUnsafe || lvls != 1 || induct.addr != p.eq.addr || cidx != 0
        || params != 2 || fields != 0 then
      throw (.other "check_eq_type: Eq.refl metadata is not canonical")
    if ty.addr != (canonicalEqReflType p).addr then
      throw (.other "check_eq_type: Eq.refl type is not canonical")
  | _ => throw (.other "check_eq_type: Eq.refl not found or not a constructor")

/-- Quot structure: address ↔ kind consistency against the primitive table,
    universe counts (1/1/2/1), exact Eq/Eq.refl prerequisites for `lift`,
    and the complete canonical type installed by Lean's `addQuot`. -/
def checkQuot (id : KId m) (kind : Ix.QuotKind) (lvls : UInt64)
    (ty : KExpr m) : RecM m Unit := do
  let p ← prims
  let expectedKind ←
    if id.addr == p.quotType.addr then pure Ix.QuotKind.type
    else if id.addr == p.quotCtor.addr then pure Ix.QuotKind.ctor
    else if id.addr == p.quotLift.addr then pure Ix.QuotKind.lift
    else if id.addr == p.quotInd.addr then pure Ix.QuotKind.ind
    else
      throw (.other s!"check_quot: unknown quot address {(toString id.addr).take 8 |>.toString}")
  if kind != expectedKind then
    throw (.other s!"check_quot: kind mismatch: declared {repr kind} but address matches {repr expectedKind}")
  let expectedLvls : UInt64 := match kind with
    | .lift => 2
    | .type | .ctor | .ind => 1
  if lvls != expectedLvls then
    throw (.other s!"check_quot: {repr kind} expects {expectedLvls} universe params, got {lvls}")
  if ty.addr != (canonicalQuotType p kind).addr then
    throw (.other s!"check_quot: {repr kind} type is not canonical")
  if kind == .lift then
    checkEqType

-- ### Block classification / coordination

/-- Ordered recursive form of the classifier's member loop. -/
def collectBlockClassFlags (members : List (KId m))
    (flags : BlockClassFlags := BlockClassFlags.empty) :
    RecM m BlockClassFlags := do
  match members with
  | [] => pure flags
  | member :: rest =>
      let c ← TcM.getConst member
      match flags.note member c with
      | .error err => throw err
      | .ok next => collectBlockClassFlags rest next
termination_by members.length

def classifyBlock (members : Array (KId m)) :
    RecM m CheckBlockKind := do
  if members.isEmpty then
    throw (.other "empty check block")
  let flags ← collectBlockClassFlags members.toList
  match flags.finish with
  | .ok kind => pure kind
  | .error err => throw err

def coordinatedBlockIfKind (block : KId m)
    (expected : CheckBlockKind) : RecM m (Option (KId m)) := do
  let some members ← TcM.tryGetBlock block | return none
  match (← try? (classifyBlock members)) with
  | some kind => if kind == expected then return some block else return none
  | none => return none

def coordinatedBlockFor (c : KConst m) : RecM m (Option (KId m)) := do
  match c with
  | .defn (block := block) .. => coordinatedBlockIfKind block .defn
  | .indc (block := block) .. => coordinatedBlockIfKind block .inductive'
  | .ctor (induct := induct) .. =>
    match (← TcM.tryGetConst induct) with
    | some (.indc (block := block) ..) =>
      coordinatedBlockIfKind block .inductive'
    | _ => return none
  | .recr (block := block) .. => coordinatedBlockIfKind block .recursor
  | .axio .. | .quot .. => return none

/-- Whole-block check key for batch schedulers. -/
def coordinatedCheckBlockForConst (id : KId m) :
    RecM m (Option (KId m)) := do
  let some c ← TcM.tryGetConst id | return none
  coordinatedBlockFor c

-- ### Checking

/-- Capture the exact outcome of a fresh block body without publishing it.
The non-backtracking checker monad retains the body's post-state on either
outcome; `checkCoordinatedBlock` performs the sole cache insertion afterward. -/
def captureBlockCheckResult (block requested : KId m) :
    RecM m (Except (TcError m) Unit) :=
  try
    checkBlockBody block requested
    pure (Except.ok ())
  catch e =>
    pure (Except.error e)

/-- Execute the coordinated suffix after routing has selected an exact
physical block.  Naming this boundary keeps the cache-hit and fresh-body
transactions visible to verification: a fresh verdict is inserted only
after `checkBlockBody` has returned, and an error verdict is then replayed as
the call's error. -/
def checkCoordinatedBlock (block requested : KId m) : RecM m Unit := do
  if let some result := (← get).env.blockCheckResults[block]? then
    match result with
    | .ok () => return ()
    | .error e => throw e
  let result ← captureBlockCheckResult block requested
  modify fun s => s.withBlockCheckResult block result
  match result with
  | .ok () => return ()
  | .error e => throw e

/-- Type-check a single constant (block-coordinated when applicable; results
    memoized in `blockCheckResults` so failures replay per member). -/
def checkConst (id : KId m) : RecM m Unit := do
  let c ← TcM.getConst id
  match (← coordinatedBlockFor c) with
  | some block => checkCoordinatedBlock block id
  | none => checkConstMemberFresh id

def checkConstMemberFresh (id : KId m) : RecM m Unit := do
  TcM.reset (m := m)
  let c ← TcM.getConst id
  checkConstMember id c

def checkConstMember (id : KId m) (c : KConst m) : RecM m Unit := do
  if Mode.F.hasDups c.levelParams then
    throw (.other "duplicate universe level parameter")
  validateConstWellScoped c
  match c with
  | .axio (ty := ty) .. =>
    let t ← infer ty
    let _ ← ensureSortDirect t
  | .defn (ty := ty) (val := val) (safety := safety) (kind := kind) .. =>
    let t ← infer ty
    let lvl ← ensureSortDirect t
    -- Theorems must have types in Prop (Sort 0).
    if kind == .thm && !univEq lvl .mkZero then
      throw (.other "theorem type must be a proposition (Sort 0)")
    let valTy ← infer val
    if !(← isDefEq valTy ty) then
      throw .declTypeMismatch
    -- Safety lattice.
    if safety != .unsaf then
      checkNoUnsafeRefs ty safety
      checkNoUnsafeRefs val safety
  | .quot (ty := ty) (kind := kind) (lvls := lvls) .. =>
    -- Reject a forged reserved primitive before invoking inference or
    -- reduction on attacker-controlled syntax.
    checkQuot id kind lvls ty
    let t ← infer ty
    let _ ← ensureSortDirect t
  | .recr (ty := ty) .. =>
    let t ← infer ty
    let _ ← ensureSortDirect t
    checkRecursorMember id
  | .indc (ty := ty) .. =>
    let t ← infer ty
    let _ ← ensureSortDirect t
    checkInductiveMember id
  | .ctor (ty := ty) (induct := induct) .. =>
    let t ← infer ty
    let _ ← ensureSortDirect t
    checkCtorAgainstInductiveMember id induct

/-- Execute the validation/checking phase after block lookup and
classification have fixed the complete member array and homogeneous kind. -/
def checkClassifiedBlock (kind : CheckBlockKind) (block : KId m)
    (members : Array (KId m)) : RecM m Unit := do
  if kind != .defn then
    for member in members do
      let c ← TcM.getConst member
      if Mode.F.hasDups c.levelParams then
        throw (.other "duplicate universe level parameter")
      validateConstWellScoped c
  match kind with
  | .defn =>
    let mut peak : UInt32 := 0
    for member in members do
      checkConstMemberFresh member
      peak := max peak (← get).defEqPeak
    let p := peak
    modify fun s => { s with defEqPeak := p }
  | .inductive' => checkInductiveBlock block members
  | .recursor => checkRecursorBlock block members

def checkBlockBody (block : KId m) (requested : KId m) :
    RecM m Unit := do
  let some members ← TcM.tryGetBlock block
    | throw (.other s!"coordinated check block {block} disappeared while checking {requested}")
  let kind ← classifyBlock members
  checkClassifiedBlock kind block members

-- ### Inductive machinery (validation and recursor generation in Ix.Tc.Inductive)

def checkInductiveMember (id : KId m) : RecM m Unit :=
  checkInductiveMemberImpl id

def checkCtorAgainstInductiveMember (id induct : KId m) :
    RecM m Unit :=
  checkCtorAgainstInductiveMemberImpl id induct

def checkInductiveBlock (block : KId m) (members : Array (KId m)) :
    RecM m Unit :=
  checkInductiveBlockImpl block members

def checkRecursorMember (id : KId m) : RecM m Unit :=
  checkRecursorMemberImpl id

def checkRecursorBlock (block : KId m) (members : Array (KId m)) :
    RecM m Unit :=
  checkRecursorBlockImpl block members

end

end RecM

namespace TcM

/-- Public entry: type-check one constant (per-constant state reset inside;
    block coordination + memoized block results).

    A failed pending check may have populated reduction or block-generation
    caches before discovering the error. `isolateCheckErrors` removes those
    subject-dependent entries at the public boundary, while preserving lazy
    loads, interning, fuel consumption, and cached block failures. -/
def checkConst (id : KId m) : TcM m Unit :=
  isolateCheckErrors (runRec (RecM.checkConst id))

end TcM

end Ix.Tc

end
end
