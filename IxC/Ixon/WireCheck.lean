module
public import IxC.Ixon.Wire
public import Std.Data.HashMap
public import Std.Data.HashSet
import all IxC.Ixon.Wire
import all IxC.Ixon.Codec

public section

namespace Ixon.WireCheck

/-- Retain the successor-prefix count while checking each universe once. -/
structure UnivSummary (u : Univ) where
  count : Nat
  count_eq : count = u.succCountNat
  valid : u.wireWF

def checkUniv : (u : Univ) → Option (UnivSummary u)
  | .zero => some ⟨0, rfl, True.intro⟩
  | .var _ => some ⟨0, rfl, True.intro⟩
  | .succ inner => do
    let child ← checkUniv inner
    if h : child.count + 1 < UInt64.size then
      return ⟨child.count + 1,
        by simp [Univ.succCountNat, child.count_eq, Nat.add_comm],
        by exact ⟨by simpa [child.count_eq, Univ.succCountNat, Nat.add_comm] using h,
          child.valid⟩⟩
    else none
  | .max left right => do
    let left ← checkUniv left
    let right ← checkUniv right
    return ⟨0, rfl, left.valid, right.valid⟩
  | .imax left right => do
    let left ← checkUniv left
    let right ← checkUniv right
    return ⟨0, rfl, left.valid, right.valid⟩

/-- Telescope counts travel with the recursive result, avoiding repeated
traversals of application and binder spines. All proof fields erase. -/
structure ExprSummary (e : Expr) where
  apps : Nat
  lams : Nat
  alls : Nat
  apps_eq : apps = e.appCount
  lams_eq : lams = e.lamCount
  alls_eq : alls = e.allCount
  valid : e.wireWF

def checkExpr : (e : Expr) → Option (ExprSummary e)
  | .sort _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .var _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .str _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .nat _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .share _ => some ⟨0, 0, 0, rfl, rfl, rfl, True.intro⟩
  | .ref _ idxs =>
    if h : idxs.size < UInt64.size then some ⟨0, 0, 0, rfl, rfl, rfl, h⟩ else none
  | .recur _ idxs =>
    if h : idxs.size < UInt64.size then some ⟨0, 0, 0, rfl, rfl, rfl, h⟩ else none
  | .prj _ _ value => do
    let value ← checkExpr value
    return ⟨0, 0, 0, rfl, rfl, rfl, value.valid⟩
  | .app fn arg => do
    let fn ← checkExpr fn
    let arg ← checkExpr arg
    if h : fn.apps + 1 < UInt64.size then
      return ⟨fn.apps + 1, 0, 0, by simp [Expr.appCount, fn.apps_eq], rfl, rfl,
        fn.valid, arg.valid, by simpa [fn.apps_eq] using h⟩
    else none
  | .lam _ ty body => do
    let ty ← checkExpr ty
    let body ← checkExpr body
    if h : body.lams + 1 < UInt64.size then
      return ⟨0, body.lams + 1, 0, rfl, by simp [Expr.lamCount, body.lams_eq], rfl,
        ty.valid, body.valid, by simpa [body.lams_eq] using h⟩
    else none
  | .all _ _ ty body => do
    let ty ← checkExpr ty
    let body ← checkExpr body
    if h : body.alls + 1 < UInt64.size then
      return ⟨0, 0, body.alls + 1, rfl, rfl, by simp [Expr.allCount, body.alls_eq],
        ty.valid, body.valid, by simpa [body.alls_eq] using h⟩
    else none
  | .letE _ ty value body => do
    let ty ← checkExpr ty
    let value ← checkExpr value
    let body ← checkExpr body
    return ⟨0, 0, 0, rfl, rfl, rfl, ty.valid, value.valid, body.valid⟩

def validUniv (u : Univ) : Bool := (checkUniv u).isSome
def validExpr (e : Expr) : Bool := (checkExpr e).isSome

def validArray (values : Array α) (valid : α → Bool) : Bool :=
  decide (values.size < UInt64.size) && values.all valid

def validDefinition (d : Definition) : Bool := validExpr d.typ && validExpr d.value

def validRecursor (r : Recursor) : Bool :=
  validExpr r.typ && validArray r.rules (fun rule => validExpr rule.rhs)

def validInductive (i : Inductive) : Bool :=
  validExpr i.typ && validArray i.ctors (fun ctor => validExpr ctor.typ)

def validMutConst : MutConst → Bool
  | .defn d => validDefinition d
  | .indc i => validInductive i
  | .recr r => validRecursor r

def validInfo : ConstantInfo → Bool
  | .defn d => validDefinition d
  | .recr r => validRecursor r
  | .axio a => validExpr a.typ
  | .quot q => validExpr q.typ
  | .cPrj p => p.block.hash.size == 32
  | .rPrj p => p.block.hash.size == 32
  | .iPrj p => p.block.hash.size == 32
  | .dPrj p => p.block.hash.size == 32
  | .muts members => validArray members validMutConst

def validBinderNode : BinderNode → Bool
  | .ifAllZero params => decide (params.size < UInt64.size)
  | _ => true

def validBinderBlock (block : BinderBlock) : Bool :=
  validArray block.nodes validBinderNode

/-- Decide exactly the production wire domain, including all side tables.
This checks representation; it does not assert typing, canonical block order,
or the binder data's canonical form (`Constant.bindersCanonical`). -/
def validConstant (constant : Constant) : Bool :=
  validInfo constant.info && validArray constant.sharing validExpr &&
    validArray constant.refs (fun address => address.hash.size == 32) &&
    validArray constant.univs validUniv &&
    validArray constant.binders validBinderBlock

end Ixon.WireCheck

namespace Ixon

/-! ## The binder data's canonical form

Two forms. The **canonical** form (`Constant.bindersCanonical`) is local, and is
what every reader checks: blocks strictly sorted by `(shared, index, variant)`, a
root block at variant 0, no empty block, every `ifAllZero` parameter list
nonempty, strictly ascending and below the record's level count, and the empty
section for a record with no root (a projection). The **complete** form
(`Constant.bindersComplete`) is what the compiler writes: the canonical form,
with exactly the blocks and nodes the record's expressions call for. The
compiler's records are complete, so their addresses are a function of the data;
a record with an incomplete section is another record, at another address, and a
checker validates every datum it reads. -/

/-- The level count bounding a record's binder data: the largest level count
of its members (0 for a projection). -/
def ConstantInfo.maxLvls : ConstantInfo → Nat
  | .defn d => d.lvls.toNat
  | .recr r => r.lvls.toNat
  | .axio a => a.lvls.toNat
  | .quot q => q.lvls.toNat
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => 0
  | .muts ms => ms.foldl (init := 0) fun acc m => max acc <| match m with
    | .defn d => d.lvls.toNat
    | .indc i => i.lvls.toNat
    | .recr r => r.lvls.toNat

/-- Strictly ascending. -/
def paramsAscending : List UInt64 → Bool
  | a :: tail@(b :: _) => a < b && paramsAscending tail
  | _ => true

/-- A node's canonical form: an `ifAllZero` parameter list is nonempty,
strictly ascending and below `lvls`. -/
def BinderNode.canonical (lvls : Nat) : BinderNode → Bool
  | .ifAllZero params =>
    !params.isEmpty && paramsAscending params.toList && params.all (·.toNat < lvls)
  | _ => true

/-- The strict `(shared, index, variant)` order of blocks (a root before a
sharing entry). -/
def BinderBlock.keyLt (a b : BinderBlock) : Bool :=
  (!a.shared && b.shared) ||
    (a.shared == b.shared &&
      (a.index < b.index || (a.index == b.index && a.variant < b.variant)))

def blocksAscending : List BinderBlock → Bool
  | a :: tail@(b :: _) => a.keyLt b && blocksAscending tail
  | _ => true

/-! ### The complete form

A record's section is complete when it holds exactly
the blocks the record's expressions call for, each with exactly one node per
numbered node, its kind matching, every share node naming a variant that the
section holds, and each sharing entry's variants pairwise distinct and
numbered in order of first occurrence. A record with no numbered node has the
empty section, and a record with one cannot: a binder whose datum is not
decided carries the undecided node, and so does every binder of an unsafe or
partial constant. So a record has one complete section for
each choice of data, and the data are the only freedom left: a checker
validates every datum it uses. -/

/-- A record's root expressions, in the order the section numbers them: a
definition's type and value; an axiom's or quotient's type; a recursor's type
and its rules' right-hand sides; an inductive's type and its constructors'
types; a block's members in order, each contributing its roots. A projection
has none. -/
def ConstantInfo.binderRoots : ConstantInfo → Array Expr
  | .defn d => #[d.typ, d.value]
  | .recr r => #[r.typ] ++ r.rules.map (·.rhs)
  | .axio a => #[a.typ]
  | .quot q => #[q.typ]
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => #[]
  | .muts ms => ms.foldl (init := #[]) fun acc m => acc ++ match m with
    | .defn d => #[d.typ, d.value]
    | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
    | .recr r => #[r.typ] ++ r.rules.map (·.rhs)

/-- Whether the record's constants are unsafe or partial: their every binder
carries the undecided node, whether or not a datum could be decided (a checker
never checks such a constant). A block's members share their safety. -/
def ConstantInfo.uncheckedSafety : ConstantInfo → Bool
  | .defn d => d.safety != .safe
  | .recr r => r.isUnsafe
  | .axio a => a.isUnsafe
  | .quot _ => false
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => false
  | .muts ms => ms.any fun m => match m with
    | .defn d => d.safety != .safe
    | .indc i => i.isUnsafe
    | .recr r => r.isUnsafe

/-- Whether `e` has a binder, directly or through the sharing entries before
it (`full`, one flag per earlier entry). -/
def Expr.hasBinderUnder (full : Array Bool) : Expr → Bool
  | .lam .. | .all .. => true
  | .app f a => f.hasBinderUnder full || a.hasBinderUnder full
  | .letE _ t v b => t.hasBinderUnder full || v.hasBinderUnder full || b.hasBinderUnder full
  | .prj _ _ v => v.hasBinderUnder full
  | .share n => full[n.toNat]?.getD false
  | _ => false

/-- Whether each sharing entry has a binder (an entry reads the entries before
it). -/
def binderfulEntries (sharing : Array Expr) : Array Bool :=
  sharing.foldl (fun out e => out.push (e.hasBinderUnder out)) #[]

/-- The numbered nodes of `e`, in pre-order (type before body, function before
argument, a `let`'s type, value, then body), appended to `acc`: `none` for a
`lam` or `all`, `some n` for a `share` of an entry `n` with a binder. A share
is not entered. -/
def Expr.numberedNodes (full : Array Bool) : Expr → Array (Option Nat) → Array (Option Nat)
  | .lam _ t b, acc => b.numberedNodes full (t.numberedNodes full (acc.push none))
  | .all _ _ t b, acc => b.numberedNodes full (t.numberedNodes full (acc.push none))
  | .app f a, acc => a.numberedNodes full (f.numberedNodes full acc)
  | .letE _ t v b, acc => b.numberedNodes full (v.numberedNodes full (t.numberedNodes full acc))
  | .prj _ _ v, acc => v.numberedNodes full acc
  | .share n, acc => if full[n.toNat]?.getD false then acc.push (some n.toNat) else acc
  | _, acc => acc

/-- The traversal state of the structure check: the blocks visited, and per
sharing entry the number of its variants met so far. -/
structure BinderWalk where
  visited : Std.HashSet (Bool × UInt64 × UInt64) := {}
  variants : Std.HashMap Nat Nat := {}

/-- Check `nodes` against the numbered nodes `shape` of their expression,
visiting each share node's variant at its first occurrence (`fuel` bounds the
nesting by the number of blocks). -/
def checkBinderNodes (lvls : Nat) (undecidedOnly : Bool) (full : Array Bool) (sharing : Array Expr)
    (blocks : Std.HashMap (Bool × UInt64 × UInt64) (Array BinderNode)) :
    Nat → Array (Option Nat) → Array BinderNode → BinderWalk → Option BinderWalk
  | 0, _, _, _ => none
  | fuel + 1, shape, nodes, walk => do
    if shape.size != nodes.size then none
    let mut walk := walk
    for (kind, node) in shape.zip nodes do
      match kind, node with
      | none, .share _ => none
      | none, node =>
        if undecidedOnly then
          unless node == .undecided do none
        else if !node.canonical lvls then none
      | some _, .never | some _, .zero | some _, .ifAllZero _ | some _, .undecided => none
      | some n, .share v =>
        let key := (true, n.toUInt64, v)
        if walk.visited.contains key then continue
        -- a new variant is the next one: variants are numbered in order of first occurrence
        if v.toNat != walk.variants.getD n 0 then none
        let some entry := sharing[n]? | none
        let some sub := blocks[key]? | none
        walk := { visited := walk.visited.insert key,
                  variants := walk.variants.insert n (v.toNat + 1) }
        walk ← checkBinderNodes lvls undecidedOnly full sharing blocks fuel (entry.numberedNodes full #[]) sub walk
    return walk

/-- The section of `c` is complete: blocks strictly sorted, exactly one per
root with a numbered node (variant 0) and per sharing entry and variant a share
node names, each matching its expression, variants numbered in order of first
occurrence and pairwise distinct. -/
/-- `bindersComplete` for a record with a root. -/
def Constant.bindersCompleteRooted (c : Constant) : Bool := Id.run do
  unless blocksAscending c.binders.toList do return false
  let lvls := c.info.maxLvls
  let full := binderfulEntries c.sharing
  let blocks : Std.HashMap (Bool × UInt64 × UInt64) (Array BinderNode) :=
    c.binders.foldl (fun m b => m.insert (b.shared, b.index, b.variant) b.nodes) {}
  let roots := c.info.binderRoots
  let mut walk : BinderWalk := {}
  for h : r in [:roots.size] do
    let shape := roots[r].numberedNodes full #[]
    if shape.isEmpty then continue
    let key := (false, r.toUInt64, (0 : UInt64))
    let some nodes := blocks[key]? | return false
    walk := { walk with visited := walk.visited.insert key }
    match checkBinderNodes lvls c.info.uncheckedSafety full c.sharing blocks (c.binders.size + 1) shape nodes walk with
    | some w => walk := w
    | none => return false
  -- no block outside the traversal
  unless walk.visited.size == c.binders.size do return false
  -- an entry's variants are distinct node lists
  for b in c.binders do
    if b.shared then
      for b' in c.binders do
        if b'.shared && b'.index == b.index && b'.variant < b.variant && b'.nodes == b.nodes then
          return false
  return true

/-- The section of `c` is complete; for a record with no root, the empty one. -/
def Constant.bindersComplete (c : Constant) : Bool :=
  if c.info.binderRoots.isEmpty then c.binders.isEmpty else c.bindersCompleteRooted

/-- The binder data of `c` are in canonical form (local): blocks strictly
sorted, a root block at variant 0, no empty block, canonical nodes, and the empty
section for a record with no root. -/
def Constant.bindersCanonical (c : Constant) : Bool :=
  if c.info.binderRoots.isEmpty then c.binders.isEmpty
  else
    blocksAscending c.binders.toList &&
      c.binders.all fun block =>
        (block.shared || block.variant == 0) && !block.nodes.isEmpty &&
          block.nodes.all (BinderNode.canonical c.info.maxLvls)

end Ixon
