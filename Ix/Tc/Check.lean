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

mutual

/-- `Eq` must exist with 1 universe param, 2 params, and `Eq.refl` as its
    single constructor (prerequisite for sound quot reduction). -/
def checkEqType : RecM m Unit := do
  let p ← prims
  let eqC? := (← get).env.consts.fold (init := none)
    fun acc id c => if id.addr == p.eq.addr then some c else acc
  let some eqC := eqC?
    | throw (.other "check_eq_type: Eq not found in environment")
  match eqC with
  | .indc (lvls := lvls) (params := params) (ctors := ctors) .. =>
    if lvls != 1 then
      throw (.other s!"check_eq_type: Eq expects 1 universe param, got {lvls}")
    if params != 2 then
      throw (.other s!"check_eq_type: Eq expects 2 params (α, a), got {params}")
    if ctors.size != 1 then
      throw (.other s!"check_eq_type: Eq expects 1 constructor, got {ctors.size}")
    if ctors[0]!.addr != p.eqRefl.addr then
      throw (.other "check_eq_type: Eq's constructor is not Eq.refl")
  | _ => throw (.other "check_eq_type: Eq not found or not inductive")

/-- Quot structure: address ↔ kind consistency against the primitive table,
    universe counts (1/1/2/1), Eq shape for `lift`, and minimum forall
    counts (2/3/6/5). -/
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
  if kind == .lift then
    checkEqType
  let expectedForalls : Nat := match kind with
    | .type => 2
    | .ctor => 3
    | .lift => 6
    | .ind => 5
  let nForalls ← countForalls ty
  if nForalls < expectedForalls then
    throw (.other s!"check_quot: {repr kind} expects at least {expectedForalls} foralls, got {nForalls}")

-- ### Block classification / coordination

def classifyBlock (members : Array (KId m)) :
    RecM m CheckBlockKind := do
  if members.isEmpty then
    throw (.other "empty check block")
  let mut sawDefn := false
  let mut sawRecr := false
  let mut sawInductiveLike := false
  for member in members do
    match (← TcM.getConst member) with
    | .defn .. => sawDefn := true
    | .recr .. => sawRecr := true
    | .indc .. | .ctor .. => sawInductiveLike := true
    | .axio .. | .quot .. =>
      throw (.other s!"unsupported check block {member}: axiom/quotient member")
  match sawDefn, sawInductiveLike, sawRecr with
  | true, false, false => return .defn
  | false, true, false => return .inductive'
  | false, false, true => return .recursor
  | _, _, _ =>
    throw (.other "unsupported mixed check block: expected only definitions, only inductives/constructors, or only recursors")

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

/-- Type-check a single constant (block-coordinated when applicable; results
    memoized in `blockCheckResults` so failures replay per member). -/
def checkConst (id : KId m) : RecM m Unit := do
  let c ← TcM.getConst id
  if let some block ← coordinatedBlockFor c then
    if let some result := (← get).env.blockCheckResults[block]? then
      match result with
      | .ok () => return ()
      | .error e => throw e
    let result ←
      try
        checkBlockBody block id
        pure (Except.ok ())
      catch e =>
        pure (Except.error e)
    modify fun s => { s with env := { s.env with
      blockCheckResults := s.env.blockCheckResults.insert block result } }
    match result with
    | .ok () => return ()
    | .error e => throw e
  checkConstMemberFresh id

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
    let t ← infer ty
    let _ ← ensureSortDirect t
    checkQuot id kind lvls ty
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

def checkBlockBody (block : KId m) (requested : KId m) :
    RecM m Unit := do
  let members := (← TcM.tryGetBlock block).getD #[requested]
  let kind ← classifyBlock members
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
