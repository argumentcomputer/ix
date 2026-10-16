/-
  Ix.Compile.Canon.Order: the structural comparator of Pass 1, total.

  The compiler's comparator (Rust `compile.rs` `compare_level` …
  `compare_const`):

  * kind tag first (definition < inductive < recursor), then the per-kind
    keys: definitions by kind, level-parameter count, type, value;
    inductives by level count, parameters, indices, constructor count, type,
    constructors pairwise (level count, index, parameters, fields, type);
    recursors by level count, parameters, indices, motives, minors, `k`,
    type, rules (field count, right-hand side);
  * expressions: binder names and binder info ignored; `letE` compares
    type, value, body, then `nonDep` (false before true), as the Rust
    compiler, the Rust kernel, `Ix.Tc` and the certified block-order check
    (`Ixon.BlockOrder.compareExpr_letE`) do; `mdata` stripped except
    semantic-contract metadata, which compares by `orderKey` (and a
    contract frame sorts after any non-contract term);
    levels compared after `Ixon.canonUniv`, parameters by position;
    constants by their level arguments first, then: the same name is equal,
    two in-block names compare by class index *weakly*, in-block sorts
    before external, two external names by compiled address (an unresolved
    name is an error, never a fall back to the name); projections the same
    way on the structure name;
  * only strong results are cached, keyed by the unordered name pair; a hit
    for the swapped pair returns the stored ordering swapped.

  Two constants of different kinds compare by kind tag, and a cached
  ordering is returned in the orientation of the call. The compiler's former
  Lean comparator did neither (it answered `lt` for every mixed-kind pair
  and returned a cached ordering as stored); no Lean input reaches the
  difference (components are kind-homogeneous, and no cached ordering is
  read back for the swapped pair inside a sort). `canon-pass1` keeps a copy
  of that comparator as its negative control and checks that the classes do
  not move.

  **Rules** carry only the seed of the refinement (`Classes.lean`):
  `byNameHash` (the refinement starts from one class sorted by the blake3
  hash of the name; `Rules.compiler`) or `allOrder` (the caller's order,
  kept stably; `canon-pass1`'s seed sweep).

  **Errors** are `CmpError`s, so the compiler's adapter
  (`Ix.CompileM.sortConsts`) can raise exactly the error the compiler's
  former comparator raised.
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.SOrder
public import Ix.SemanticContract
public import Ix.IxonUniv
public import Ix.Compile.Canon.Expr
@[expose] public section

namespace Ix.Compile.Canon

open Ix (Name Level Expr MutConst Def Ind Rec MutCtx ConstructorVal RecursorVal
  RecursorRule)

/-! ## Rules -/

/-- Where the refinement starts. -/
inductive Seed where
  /-- One class sorted by the blake3 hash of the name. -/
  | byNameHash
  /-- The caller's order (Lean's `all`, a clique's member order), kept
  stably. -/
  | allOrder
  deriving BEq, Repr, Inhabited

/-- What a refinement is parameterised by: its seed. -/
structure Rules where
  seed : Seed := .byNameHash
  deriving BEq, Repr, Inhabited

/-- The compiler's rules: the name-hash seed. -/
def Rules.compiler : Rules := {}

/-- What one comparison needs: the external addresses and the current class
index of every in-block name. -/
structure CmpCtx where
  addr? : Name → Option Address
  mutCtx : MutCtx

/-- Why a comparison or a refinement failed. -/
inductive CmpError where
  /-- A level metavariable. -/
  | levelMVar
  /-- An expression metavariable. -/
  | exprMVar
  /-- A free variable. -/
  | fvar
  /-- A level parameter outside the constant's parameter list. -/
  | unknownUnivParam (param : Name)
  /-- Semantic-contract metadata that does not read. -/
  | contract (msg : String)
  /-- An external constant without a compiled address. -/
  | missingAddress (name : Name)
  /-- A guard of the refinement itself (an empty class, no fixed point
  within the fuel, more classes than members). -/
  | refinement (msg : String)
  deriving Inhabited

def CmpError.render : CmpError → String
  | .levelMVar => "level metavariable in comparison"
  | .exprMVar => "metavariable in comparison"
  | .fvar => "fvar in comparison"
  | .unknownUnivParam p => s!"unknown universe parameter {namePretty p}"
  | .contract msg => msg
  | .missingAddress n => s!"no compiled address for {namePretty n}"
  | .refinement msg => msg

instance : ToString CmpError := ⟨CmpError.render⟩

/-! ## Levels -/

/-- A level as an `Ixon.Univ`, parameters by position. -/
def toUniv (ctx : List Name) : Level → Except CmpError Ixon.Univ
  | .zero _ => pure .zero
  | .succ l _ => .succ <$> toUniv ctx l
  | .max a b _ => .max <$> toUniv ctx a <*> toUniv ctx b
  | .imax a b _ => .imax <$> toUniv ctx a <*> toUniv ctx b
  | .param n _ =>
    match ctx.idxOf? n with
    | some i => pure (.var i.toUInt64)
    | none => .error (.unknownUnivParam n)
  | .mvar .. => .error .levelMVar

/-- Structural order on `Ixon.Univ`: `zero < succ < max < imax < var`,
then the arguments left to right. -/
def compareUniv : Ixon.Univ → Ixon.Univ → Ordering
  | .zero, .zero => .eq
  | .zero, _ => .lt
  | _, .zero => .gt
  | .succ x, .succ y => compareUniv x y
  | .succ _, _ => .lt
  | _, .succ _ => .gt
  | .max a b, .max c d => (compareUniv a c).then (compareUniv b d)
  | .max .., _ => .lt
  | _, .max .. => .gt
  | .imax a b, .imax c d => (compareUniv a c).then (compareUniv b d)
  | .imax .., _ => .lt
  | _, .imax .. => .gt
  | .var i, .var j => compare i j

/-- Two levels, compared after `Ixon.canonUniv` with parameters by position
in `xctx` and `yctx` (the serializer's normal form). -/
def compareLevel (xctx yctx : List Name) (x y : Level) : Except CmpError SOrder := do
  let ux ← toUniv xctx x
  let uy ← toUniv yctx y
  pure ⟨true, compareUniv (Ixon.canonUniv ux) (Ixon.canonUniv uy)⟩

/-- `SOrder.zipM` specialised (pointwise, then by length). -/
def compareLevels (xctx yctx : List Name) : List Level → List Level → Except CmpError SOrder :=
  SOrder.zipM (compareLevel xctx yctx)

/-! ## Expressions -/

def exprSize : Expr → Nat
  | .bvar .. | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => 1
  | .app f a _ => exprSize f + exprSize a + 1
  | .lam _ t b _ _ | .forallE _ t b _ _ => exprSize t + exprSize b + 1
  | .letE _ t v b _ _ => exprSize t + exprSize v + exprSize b + 1
  | .proj _ _ s _ | .mdata _ s _ => exprSize s + 1

@[simp] theorem exprSize_app (f a : Expr) (h : Address) :
    exprSize (.app f a h) = exprSize f + exprSize a + 1 := by rfl
@[simp] theorem exprSize_lam (n : Name) (t b : Expr) (bi : Lean.BinderInfo)
    (h : Address) : exprSize (.lam n t b bi h) = exprSize t + exprSize b + 1 := by rfl
@[simp] theorem exprSize_forallE (n : Name) (t b : Expr) (bi : Lean.BinderInfo)
    (h : Address) : exprSize (.forallE n t b bi h) = exprSize t + exprSize b + 1 := by rfl
@[simp] theorem exprSize_letE (n : Name) (t v b : Expr) (nd : Bool) (h : Address) :
    exprSize (.letE n t v b nd h) = exprSize t + exprSize v + exprSize b + 1 := by rfl
@[simp] theorem exprSize_proj (n : Name) (i : Nat) (s : Expr) (h : Address) :
    exprSize (.proj n i s h) = exprSize s + 1 := by rfl
@[simp] theorem exprSize_mdata (d : Array (Name × Ix.DataValue)) (s : Expr)
    (h : Address) : exprSize (.mdata d s h) = exprSize s + 1 := by rfl

/-- Two external names, by compiled address. -/
def compareExternal (c : CmpCtx) (x y : Name) : Except CmpError SOrder :=
  match c.addr? x, c.addr? y with
  | some ax, some ay => pure ⟨true, compare ax ay⟩
  | none, _ => .error (.missingAddress x)
  | _, none => .error (.missingAddress y)

/-- Two referenced names (constant heads after their levels, or projection
structures): same name equal; in-block by class index, weakly; in-block
before external; external by `compareExternal`. -/
def compareRef (c : CmpCtx) (x y : Name) : Except CmpError SOrder :=
  if x == y then pure ⟨true, .eq⟩
  else match c.mutCtx.get? x, c.mutCtx.get? y with
    | some nx, some ny => pure ⟨false, compare nx ny⟩
    | some _, none => pure ⟨true, .lt⟩
    | none, some _ => pure ⟨true, .gt⟩
    | none, none => compareExternal c x y

/-- The name-irrelevant structural order on expressions (the compiler's
`compareExpr`). -/
def compareExpr (c : CmpCtx) (xl yl : List Name) (x y : Expr) :
    Except CmpError SOrder :=
  match x, y with
  | .mvar .., _ | _, .mvar .. => .error .exprMVar
  | .fvar .., _ | _, .fvar .. => .error .fvar
  | .mdata dx xi hx, .mdata dy yi hy =>
    if SemanticContract.hasMetadata dx then
      if SemanticContract.hasMetadata dy then do
        let cx ← (SemanticContract.read dx).mapError CmpError.contract
        let cy ← (SemanticContract.read dy).mapError CmpError.contract
        let o := compare cx.orderKey cy.orderKey
        if o != .eq then pure ⟨true, o⟩ else compareExpr c xl yl xi yi
      else compareExpr c xl yl (.mdata dx xi hx) yi
    else compareExpr c xl yl xi (.mdata dy yi hy)
  | .mdata d x _, y =>
    if SemanticContract.hasMetadata d then pure ⟨true, .gt⟩
    else compareExpr c xl yl x y
  | x, .mdata d y _ =>
    if SemanticContract.hasMetadata d then pure ⟨true, .lt⟩
    else compareExpr c xl yl x y
  | .bvar i _, .bvar j _ => pure ⟨true, compare i j⟩
  | .bvar .., _ => pure ⟨true, .lt⟩
  | _, .bvar .. => pure ⟨true, .gt⟩
  | .sort u _, .sort v _ => compareLevel xl yl u v
  | .sort .., _ => pure ⟨true, .lt⟩
  | _, .sort .. => pure ⟨true, .gt⟩
  | .const xn xls _, .const yn yls _ => do
    let us ← compareLevels xl yl xls.toList yls.toList
    if us.ord != .eq then pure us else compareRef c xn yn
  | .const .., _ => pure ⟨true, .lt⟩
  | _, .const .. => pure ⟨true, .gt⟩
  | .app xf xa _, .app yf ya _ =>
    SOrder.cmpM (compareExpr c xl yl xf yf) (compareExpr c xl yl xa ya)
  | .app .., _ => pure ⟨true, .lt⟩
  | _, .app .. => pure ⟨true, .gt⟩
  | .lam _ xt xb _ _, .lam _ yt yb _ _ =>
    SOrder.cmpM (compareExpr c xl yl xt yt) (compareExpr c xl yl xb yb)
  | .lam .., _ => pure ⟨true, .lt⟩
  | _, .lam .. => pure ⟨true, .gt⟩
  | .forallE _ xt xb _ _, .forallE _ yt yb _ _ =>
    SOrder.cmpM (compareExpr c xl yl xt yt) (compareExpr c xl yl xb yb)
  | .forallE .., _ => pure ⟨true, .lt⟩
  | _, .forallE .. => pure ⟨true, .gt⟩
  | .letE _ xt xv xb xnd _, .letE _ yt yv yb ynd _ =>
    SOrder.cmpM (compareExpr c xl yl xt yt) <|
      SOrder.cmpM (compareExpr c xl yl xv yv) <|
        SOrder.cmpM (compareExpr c xl yl xb yb) (pure ⟨true, compare xnd ynd⟩)
  | .letE .., _ => pure ⟨true, .lt⟩
  | _, .letE .. => pure ⟨true, .gt⟩
  | .lit a _, .lit b _ => pure ⟨true, compare a b⟩
  | .lit .., _ => pure ⟨true, .lt⟩
  | _, .lit .. => pure ⟨true, .gt⟩
  | .proj xn xi xs _, .proj yn yi ys _ =>
    SOrder.cmpM (compareRef c xn yn) <|
      SOrder.cmpM (pure ⟨true, compare xi yi⟩) (compareExpr c xl yl xs ys)
termination_by exprSize x + exprSize y
decreasing_by
  all_goals simp only [exprSize_app, exprSize_lam, exprSize_forallE,
    exprSize_letE, exprSize_proj, exprSize_mdata]
  all_goals omega

/-! ## Constants -/

/-- The comparison cache: unordered name pair ↦ the ordering and the name
that was on the left when it was computed. -/
structure CmpState where
  cache : Std.HashMap (Name × Name) (Ordering × Name) := {}
  deriving Inhabited

abbrev CmpM := StateT CmpState (Except CmpError)

def liftE (x : Except CmpError α) : CmpM α := liftM x

def cacheKey (x y : Name) : Name × Name :=
  match compare x y with
  | .lt => (x, y)
  | _ => (y, x)

/-- Look up the cache, in the orientation of the call: a hit computed for the
swapped pair is returned swapped. -/
def cacheGet (x y : Name) : CmpM (Option Ordering) := do
  match (← get).cache.get? (cacheKey x y) with
  | none => pure none
  | some (o, left) => pure (some (if left == x then o else o.swap))

def cachePut (x y : Name) (o : SOrder) : CmpM Unit :=
  if o.strong then
    modify fun st => { st with cache := st.cache.insert (cacheKey x y) (o.ord, x) }
  else pure ()

def compareDef (c : CmpCtx) (x y : Def) : Except CmpError SOrder :=
  SOrder.cmpM (pure ⟨true, compare x.kind y.kind⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.levelParams.size y.levelParams.size⟩) <|
  SOrder.cmpM (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
    (compareExpr c x.levelParams.toList y.levelParams.toList x.value y.value)

/-- A constructor's own keys, uncached. -/
def compareCtorKeys (c : CmpCtx) (xl yl : List Name) (x y : ConstructorVal) :
    Except CmpError SOrder :=
  SOrder.cmpM (pure ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.cidx y.cidx⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numFields y.numFields⟩)
    (compareExpr c xl yl x.cnst.type y.cnst.type)

def compareCtor (c : CmpCtx) (xl yl : List Name) (x y : ConstructorVal) : CmpM SOrder := do
  if let some o ← cacheGet x.cnst.name y.cnst.name then
    return ⟨true, o⟩
  let so ← liftE (compareCtorKeys c xl yl x y)
  cachePut x.cnst.name y.cnst.name so
  return so

def compareCtors (c : CmpCtx) (xl yl : List Name) :
    List ConstructorVal → List ConstructorVal → CmpM SOrder :=
  SOrder.zipM (compareCtor c xl yl)

/-- An inductive's header: level count, parameters, indices, constructor
count. -/
def indHeader (x y : Ind) : SOrder :=
  SOrder.cmpMany ⟨true, compare x.levelParams.size y.levelParams.size⟩
    [⟨true, compare x.numParams y.numParams⟩,
     ⟨true, compare x.numIndices y.numIndices⟩,
     ⟨true, compare x.ctors.size y.ctors.size⟩]

def compareInd (c : CmpCtx) (x y : Ind) : CmpM SOrder := do
  let xl := x.levelParams.toList
  let yl := y.levelParams.toList
  let hdr := indHeader x y
  match hdr with
  | ⟨true, .eq⟩ => pure ()
  | o => if o.ord != .eq then return o else pure ()
  let ty ← liftE (compareExpr c xl yl x.type y.type)
  let ty := SOrder.cmp hdr ty
  if ty.ord != .eq then return ty
  let cs ← compareCtors c xl yl x.ctors.toList y.ctors.toList
  return SOrder.cmp ty cs

def compareRule (c : CmpCtx) (xl yl : List Name) (x y : RecursorRule) :
    Except CmpError SOrder :=
  SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩) (compareExpr c xl yl x.rhs y.rhs)

def compareRecr (c : CmpCtx) (x y : RecursorVal) : Except CmpError SOrder :=
  let xl := x.cnst.levelParams.toList
  let yl := y.cnst.levelParams.toList
  SOrder.cmpM (pure ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numIndices y.numIndices⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numMotives y.numMotives⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.numMinors y.numMinors⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.k y.k⟩) <|
  SOrder.cmpM (compareExpr c xl yl x.cnst.type y.cnst.type)
    (SOrder.zipM (compareRule c xl yl) x.rules.toList y.rules.toList)

def kindTag : MutConst → Nat
  | .defn _ => 0
  | .indc _ => 1
  | .recr _ => 2

/-- Variant dispatch; two constants of different kinds compare by kind tag
(Rust `compile.rs` `mut_const_kind`). -/
def compareConstBody (c : CmpCtx) (x y : MutConst) : CmpM SOrder :=
  match x, y with
  | .defn x, .defn y => liftE (compareDef c x y)
  | .indc x, .indc y => compareInd c x y
  | .recr x, .recr y => liftE (compareRecr c x y)
  | x, y => pure ⟨true, compare (kindTag x) (kindTag y)⟩

/-- The comparison the refinement sorts by, cached. -/
def compareConst (addr? : Name → Option Address) (mutCtx : MutCtx) (x y : MutConst) :
    CmpM Ordering := do
  if let some o ← cacheGet x.name y.name then
    return o
  let so ← compareConstBody { addr?, mutCtx } x y
  cachePut x.name y.name so
  return so.ord

end Ix.Compile.Canon

end
