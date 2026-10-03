/-
  Ix.Compile.Canon.Order: the structural comparator of Pass 1, total.

  Same structure as today's `compareLevel`/`compareExpr`/`compareDef`/
  `compareCtor`/`compareInd`/`compareRecr`/`compareConst`
  (`Ix/CompileM.lean:1983-2245`; Rust `compile.rs:3153-3640`):

  * kind tag first (definition < inductive < recursor), then the per-kind
    keys: definitions by kind, level-parameter count, type, value;
    inductives by level count, parameters, indices, constructor count, type,
    constructors pairwise (level count, index, parameters, fields, type);
    recursors by level count, parameters, indices, motives, minors, `k`,
    type, rules (field count, right-hand side);
  * expressions: binder names and binder info ignored; `mdata` stripped
    except semantic-contract metadata, which compares by `orderKey` (and a
    contract frame sorts after any non-contract term); level parameters by
    position; constants by their level arguments first, then: the same name
    is equal, two in-block names compare by class index *weakly*, in-block
    sorts before external, two external names by compiled address
    (`ExtMode.addr`; an unresolved name is an error, never a fall back to the
    name); projections the same way on the structure name;
  * only strong results are cached, keyed by the unordered name pair.

  **Rule sets** (`Rules`): `Rules.today` reproduces the compiler as it was;
  `Rules.compiler` is what the compiler runs now (today plus the port
  fixes); `Rules.phaseA` is the Phase A decision set
  (`PLAN-A-compiler-design.md` §3.1, owner's decisions of 2026-10-03 on Q1
  and Q2): today's comparator (external references by address at the first
  difference), today's name-hash seed and least-name-hash representative,
  plus levels after `canonUniv`, nested auxiliaries in discovery order and
  the port fixes. The other switches remain for measurement only:
  * `seed`: `byNameHash` (today and Phase A: the refinement starts from one
    class sorted by the blake3 hash of the name) or `allOrder` (the caller's
    order: Lean's `all` restricted to the component, or `EqnInfo.declNames`
    for a clique, kept stably; used by the seed sweep);
  * `levels`: `syntactic` (today) or `afterCanonUniv` (levels compared after
    `Ixon.canonUniv`, with parameters by position);
  * `representative`: `leastNameHash` (today and Phase A: every group
    re-sorted by name hash, so the first member has the least name hash) or
    `firstInCanonicalOrder` (first member in the stable order);
  * `tieBreak`: `inline` (today and Phase A: external references compare by
    address wherever they occur, at the first difference), `byAddress` (the
    considered and rejected lexicographic pair `(k₀, k₁)`, `k₀` with every
    external reference equal and `k₁` today's key; the partition is `k₁`'s,
    only the class order can move; comparisons that `k₀` ties and `k₁`
    decides are counted), or `blind` (never use addresses: the census's
    order-stability probe);
  * `nested`: the order of nested auxiliaries, `structural` (today) or
    `discovery` (Lean's), used by `Nested.lean`.

  **Port defects** (design document §3.4, C1 and C2). Today's Lean cache is
  keyed by the unordered name pair but stores and returns the ordering in
  the orientation of the call that computed it (Rust normalises it,
  `compile.rs` `compare_const`, `compare_ctor`); and Lean's
  `compareConstBody` answers `lt` for every mixed-kind pair (Rust compares
  kind tags). With `portFixes := false` (`Rules.today`) both are mirrored and
  every reversed non-equal cache hit is counted in `CmpState.hazards`; with
  `portFixes := true` both are fixed as in Rust.
-/
module
public import Ix.Environment
public import Ix.Mutual
public import Ix.SOrder
public import Ix.SemanticContract
public import Ix.IxonUniv
public import Ix.Compile.Canon.Expr
public section

namespace Ix.Compile.Canon

open Ix (Name Level Expr MutConst Def Ind Rec MutCtx ConstructorVal RecursorVal
  RecursorRule)

/-! ## Rule sets -/

inductive Seed where
  | byNameHash
  | allOrder
  deriving BEq, Repr, Inhabited

inductive LevelCompare where
  | syntactic
  | afterCanonUniv
  deriving BEq, Repr, Inhabited

inductive Representative where
  | leastNameHash
  | firstInCanonicalOrder
  deriving BEq, Repr, Inhabited

inductive TieBreak where
  | inline
  | byAddress
  | blind
  deriving BEq, Repr, Inhabited

inductive NestedOrder where
  | structural
  | discovery
  deriving BEq, Repr, Inhabited

structure Rules where
  seed : Seed
  levels : LevelCompare
  representative : Representative
  tieBreak : TieBreak
  nested : NestedOrder
  /-- The two Lean-port comparator defects fixed as in Rust (design
  document §3.4): C1, mixed kinds by kind tag; C2, the cache normalised to
  the key's orientation. Off only for `Rules.today`, which mirrors the port;
  required by any seed other than the name hash. -/
  portFixes : Bool := true
  deriving BEq, Repr, Inhabited

/-- Today's compiler. -/
def Rules.today : Rules :=
  ⟨.byNameHash, .syntactic, .leastNameHash, .inline, .structural, false⟩

/-- What the compiler runs (A2's byte-neutral half): today's rules with the
two Lean-port comparator defects fixed (C1 and C2, owner's decision of
2026-10-03). Neither fix is reachable on Lean input (components are
kind-homogeneous; every class is sorted in name-hash order, so a cached
ordering is never read back for the swapped pair inside the sort), so the
output is `Rules.today`'s. -/
def Rules.compiler : Rules := { Rules.today with portFixes := true }

/-- The Phase A decisions (`PLAN-A-compiler-design.md` §3.1; owner, 2026-10-03:
first-difference address comparison, name-hash seed and representative kept). -/
def Rules.phaseA : Rules :=
  ⟨.byNameHash, .afterCanonUniv, .leastNameHash, .inline, .discovery, true⟩

/-- Today's rules with only the tie-break changed to `(k₀, k₁)`. -/
def Rules.todayK : Rules := { Rules.today with tieBreak := .byAddress, portFixes := true }

/-- Today's rules with only the levels compared after `canonUniv`. -/
def Rules.todayU : Rules := { Rules.today with levels := .afterCanonUniv, portFixes := true }

def Rules.name (r : Rules) : String :=
  if r == .today then "today" else if r == .phaseA then "phaseA"
  else if r == .compiler then "compiler"
  else if r == .todayK then "today+(k0,k1)" else if r == .todayU then "today+canonUniv"
  else reprStr r

/-- How a comparison treats two different external constants. -/
inductive ExtMode where
  /-- By compiled address (an unresolved name is an error). -/
  | addr
  /-- As equal: the address-free relation. -/
  | blind
  deriving BEq, Repr, Inhabited

/-- What one comparison needs: the level rule, the external mode, the
external addresses and the current class index of every in-block name. -/
structure CmpCtx where
  levels : LevelCompare
  mode : ExtMode
  addr? : Name → Option Address
  mutCtx : MutCtx

/-! ## Levels -/

/-- Syntactic level comparison with parameters by position
(`Ix.CompileM.compareLevel`). -/
def compareLevelSyn (xctx yctx : List Name) : Level → Level → Except String SOrder
  | .mvar .., _ | _, .mvar .. => .error "level metavariable in comparison"
  | .zero _, .zero _ => pure ⟨true, .eq⟩
  | .zero _, _ => pure ⟨true, .lt⟩
  | _, .zero _ => pure ⟨true, .gt⟩
  | .succ x _, .succ y _ => compareLevelSyn xctx yctx x y
  | .succ .., _ => pure ⟨true, .lt⟩
  | _, .succ .. => pure ⟨true, .gt⟩
  | .max xl xr _, .max yl yr _ =>
    SOrder.cmpM (compareLevelSyn xctx yctx xl yl) (compareLevelSyn xctx yctx xr yr)
  | .max .., _ => pure ⟨true, .lt⟩
  | _, .max .. => pure ⟨true, .gt⟩
  | .imax xl xr _, .imax yl yr _ =>
    SOrder.cmpM (compareLevelSyn xctx yctx xl yl) (compareLevelSyn xctx yctx xr yr)
  | .imax .., _ => pure ⟨true, .lt⟩
  | _, .imax .. => pure ⟨true, .gt⟩
  | .param x _, .param y _ =>
    match xctx.idxOf? x, yctx.idxOf? y with
    | some xi, some yi => pure ⟨true, compare xi yi⟩
    | none, _ => .error s!"unknown universe parameter {namePretty x}"
    | _, none => .error s!"unknown universe parameter {namePretty y}"

/-- A level as an `Ixon.Univ`, parameters by position. -/
def toUniv (ctx : List Name) : Level → Except String Ixon.Univ
  | .zero _ => pure .zero
  | .succ l _ => .succ <$> toUniv ctx l
  | .max a b _ => .max <$> toUniv ctx a <*> toUniv ctx b
  | .imax a b _ => .imax <$> toUniv ctx a <*> toUniv ctx b
  | .param n _ =>
    match ctx.idxOf? n with
    | some i => pure (.var i.toUInt64)
    | none => .error s!"unknown universe parameter {namePretty n}"
  | .mvar .. => .error "level metavariable in comparison"

/-- Structural order on `Ixon.Univ` with the constructor order of
`compareLevelSyn`. -/
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

def compareLevel (lc : LevelCompare) (xctx yctx : List Name) (x y : Level) :
    Except String SOrder :=
  match lc with
  | .syntactic => compareLevelSyn xctx yctx x y
  | .afterCanonUniv => do
    let ux ← toUniv xctx x
    let uy ← toUniv yctx y
    pure ⟨true, compareUniv (Ixon.canonUniv ux) (Ixon.canonUniv uy)⟩

/-- `SOrder.zipM` specialised (pointwise, then by length). -/
def compareLevels (lc : LevelCompare) (xctx yctx : List Name) :
    List Level → List Level → Except String SOrder :=
  SOrder.zipM (compareLevel lc xctx yctx)

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

/-- Two external names. -/
def compareExternal (c : CmpCtx) (x y : Name) : Except String SOrder :=
  match c.mode with
  | .blind => pure ⟨true, .eq⟩
  | .addr =>
    match c.addr? x, c.addr? y with
    | some ax, some ay => pure ⟨true, compare ax ay⟩
    | none, _ => .error s!"no compiled address for {namePretty x}"
    | _, none => .error s!"no compiled address for {namePretty y}"

/-- Two referenced names (constant heads after their levels, or projection
structures): same name equal; in-block by class index, weakly; in-block
before external; external by `compareExternal`. -/
def compareRef (c : CmpCtx) (x y : Name) : Except String SOrder :=
  if x == y then pure ⟨true, .eq⟩
  else match c.mutCtx.get? x, c.mutCtx.get? y with
    | some nx, some ny => pure ⟨false, compare nx ny⟩
    | some _, none => pure ⟨true, .lt⟩
    | none, some _ => pure ⟨true, .gt⟩
    | none, none => compareExternal c x y

/-- The name-irrelevant structural order on expressions
(`Ix.CompileM.compareExpr`). -/
def compareExpr (c : CmpCtx) (xl yl : List Name) (x y : Expr) :
    Except String SOrder :=
  match x, y with
  | .mvar .., _ | _, .mvar .. => .error "metavariable in comparison"
  | .fvar .., _ | _, .fvar .. => .error "fvar in comparison"
  | .mdata dx xi hx, .mdata dy yi hy =>
    if SemanticContract.hasMetadata dx then
      if SemanticContract.hasMetadata dy then do
        let cx ← SemanticContract.read dx
        let cy ← SemanticContract.read dy
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
  | .sort u _, .sort v _ => compareLevel c.levels xl yl u v
  | .sort .., _ => pure ⟨true, .lt⟩
  | _, .sort .. => pure ⟨true, .gt⟩
  | .const xn xls _, .const yn yls _ => do
    let us ← compareLevels c.levels xl yl xls.toList yls.toList
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
  | .letE _ xt xv xb _ _, .letE _ yt yv yb _ _ =>
    SOrder.cmpM (compareExpr c xl yl xt yt) <|
      SOrder.cmpM (compareExpr c xl yl xv yv) (compareExpr c xl yl xb yb)
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

/-- The comparison cache: unordered name pair (and external mode) ↦ the
ordering and the name that was on the left when it was computed. -/
structure CmpState where
  cache : Std.HashMap (Bool × Name × Name) (Ordering × Name) := {}
  /-- Cache hits for the reversed pair with a non-equal stored ordering. -/
  hazards : Nat := 0
  /-- `byAddress` comparisons that were address-free equal and decided by
  addresses. -/
  addrDecided : Nat := 0
  deriving Inhabited

abbrev CmpM := StateT CmpState (Except String)

def liftE (x : Except String α) : CmpM α := liftM x

def cacheKey (blind : Bool) (x y : Name) : Bool × Name × Name :=
  match compare x y with
  | .lt => (blind, x, y)
  | _ => (blind, y, x)

/-- Look up the cache; `flip` says whether a reversed hit is flipped (Rust)
or returned as stored (today's Lean). -/
def cacheGet (flip : Bool) (blind : Bool) (x y : Name) : CmpM (Option Ordering) := do
  let st ← get
  match st.cache.get? (cacheKey blind x y) with
  | none => pure none
  | some (o, left) =>
    if left == x || o == .eq then pure (some o)
    else do
      set { st with hazards := st.hazards + 1 }
      pure (some (if flip then o.swap else o))

def cachePut (blind : Bool) (x y : Name) (o : SOrder) : CmpM Unit :=
  if o.strong then
    modify fun st => { st with cache := st.cache.insert (cacheKey blind x y) (o.ord, x) }
  else pure ()

def compareDef (c : CmpCtx) (x y : Def) : Except String SOrder :=
  SOrder.cmpM (pure ⟨true, compare x.kind y.kind⟩) <|
  SOrder.cmpM (pure ⟨true, compare x.levelParams.size y.levelParams.size⟩) <|
  SOrder.cmpM (compareExpr c x.levelParams.toList y.levelParams.toList x.type y.type)
    (compareExpr c x.levelParams.toList y.levelParams.toList x.value y.value)

def compareCtor (flip : Bool) (c : CmpCtx) (xl yl : List Name)
    (x y : ConstructorVal) : CmpM SOrder := do
  let blind := c.mode == .blind
  if let some o ← cacheGet flip blind x.cnst.name y.cnst.name then
    return ⟨true, o⟩
  let so ← liftE <|
    SOrder.cmpM (pure ⟨true, compare x.cnst.levelParams.size y.cnst.levelParams.size⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.cidx y.cidx⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numParams y.numParams⟩) <|
    SOrder.cmpM (pure ⟨true, compare x.numFields y.numFields⟩)
      (compareExpr c xl yl x.cnst.type y.cnst.type)
  cachePut blind x.cnst.name y.cnst.name so
  return so

def compareCtors (flip : Bool) (c : CmpCtx) (xl yl : List Name) :
    List ConstructorVal → List ConstructorVal → CmpM SOrder :=
  SOrder.zipM (compareCtor flip c xl yl)

def compareInd (flip : Bool) (c : CmpCtx) (x y : Ind) : CmpM SOrder := do
  let xl := x.levelParams.toList
  let yl := y.levelParams.toList
  let hdr : SOrder :=
    SOrder.cmpMany ⟨true, compare x.levelParams.size y.levelParams.size⟩
      [⟨true, compare x.numParams y.numParams⟩,
       ⟨true, compare x.numIndices y.numIndices⟩,
       ⟨true, compare x.ctors.size y.ctors.size⟩]
  match hdr with
  | ⟨true, .eq⟩ => pure ()
  | o => if o.ord != .eq then return o else pure ()
  let ty ← liftE (compareExpr c xl yl x.type y.type)
  let ty := SOrder.cmp hdr ty
  if ty.ord != .eq then return ty
  let cs ← compareCtors flip c xl yl x.ctors.toList y.ctors.toList
  return SOrder.cmp ty cs

def compareRule (c : CmpCtx) (xl yl : List Name) (x y : RecursorRule) :
    Except String SOrder :=
  SOrder.cmpM (pure ⟨true, compare x.nfields y.nfields⟩) (compareExpr c xl yl x.rhs y.rhs)

def compareRecr (c : CmpCtx) (x y : RecursorVal) : Except String SOrder :=
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

/-- Variant dispatch. Two constants of different kinds: today's Lean answers
`lt` whatever the order of the arguments (`Ix/CompileM.lean`
`compareConstBody`: `.indc _, _ => lt`, `.recr _, _ => lt`), which is not
antisymmetric; Rust compares the kind tags (`compile.rs` `mut_const_kind`).
`kindsByTag := false` mirrors Lean, `true` compares tags. Lean never puts
two kinds in one component, so the difference is latent. -/
def compareConstBody (kindsByTag flip : Bool) (c : CmpCtx) (x y : MutConst) :
    CmpM SOrder :=
  match x, y with
  | .defn x, .defn y => liftE (compareDef c x y)
  | .indc x, .indc y => compareInd flip c x y
  | .recr x, .recr y => liftE (compareRecr c x y)
  | x, y =>
    if kindsByTag then pure ⟨true, compare (kindTag x) (kindTag y)⟩
    else pure ⟨true, .lt⟩

/-- One cached comparison in one external mode (`Ix.CompileM.compareConst`). -/
def compareConstIn (flip : Bool) (c : CmpCtx) (x y : MutConst) : CmpM Ordering := do
  let blind := c.mode == .blind
  if let some o ← cacheGet flip blind x.name y.name then
    return o
  let so ← compareConstBody flip flip c x y -- `flip` is `portFixes`
  cachePut blind x.name y.name so
  return so.ord

/-- The comparison a rule set sorts by. -/
def compareConst (rules : Rules) (addr? : Name → Option Address) (mutCtx : MutCtx)
    (x y : MutConst) : CmpM Ordering := do
  let flip := rules.portFixes
  let c : CmpCtx := { levels := rules.levels, mode := .addr, addr?, mutCtx }
  match rules.tieBreak with
  | .inline => compareConstIn flip c x y
  | .blind => compareConstIn flip { c with mode := .blind } x y
  | .byAddress =>
    let b ← compareConstIn flip { c with mode := .blind } x y
    if b != .eq then return b
    let a ← compareConstIn flip c x y
    if a != .eq then modify fun st => { st with addrDecided := st.addrDecided + 1 }
    return a

end Ix.Compile.Canon

end
