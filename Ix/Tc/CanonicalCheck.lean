module

public import Ix.Tc.Const
public import Ix.Tc.Error

/-!
Mirror: crates/kernel/src/canonical_check.rs

Kernel-side canonical-block validation — the compile-side `sort_consts`
machinery replicated so the kernel can independently verify that stored
mutual blocks ship in canonical (alpha-collapsed, structurally sorted)
order, and so `canonicalAuxOrder` can re-derive the compiler's nested-aux
permutation:

1. `validateCanonicalBlockSinglePass` — treats the stored order as the
   alleged canonical partition and checks adjacent pairs are strictly
   strong-`lt`. `gt` (wrong order) and `eq` (uncollapsed alpha-equivalence)
   reject; a weak `lt` falls back to full iterative refinement.
2. `sortKConsts` / `sortKConstsWithSeedKey` — iterative partition
   refinement (sort → group → re-sort under updated `KMutCtx`) to fixpoint;
   returns canonical equivalence classes.

Both share the comparators (`compareKConst`/`compareKExpr`/`compareKUniv`)
keyed on a `KMutCtx` mapping block-local addresses to class indices:
ctx hits compare positionally (weak), misses fall back to address order
(strong). Field orders match `src/ix/compile.rs` comparators exactly.
-/

public section
@[expose] section

namespace Ix.Tc

open Std (HashMap)

/-- Strong ordering: an `Ordering` plus whether it was decided by strong
    (structural) evidence or weakly via the current partition. Mirrors
    `ix_common::strong_ordering::SOrd`. -/
structure SOrd where
  strong : Bool
  ordering : Ordering
  deriving BEq, Repr, Inhabited

namespace SOrd

def eq' (strong : Bool) : SOrd := ⟨strong, .eq⟩
def lt' (strong : Bool) : SOrd := ⟨strong, .lt⟩
def gt' (strong : Bool) : SOrd := ⟨strong, .gt⟩

/-- Sequence: an `eq` defers to `other`, propagating weakness. -/
def andThen (s other : SOrd) : SOrd :=
  match s with
  | ⟨true, .eq⟩ => other
  | ⟨false, .eq⟩ => ⟨false, other.ordering⟩
  | _ => s

/-- Strong compare of an `Ordering` result. -/
def ofOrdering (o : Ordering) : SOrd := ⟨true, o⟩

/-- Weak compare of an `Ordering` result (partition-derived). -/
def weakOfOrdering (o : Ordering) : SOrd := ⟨false, o⟩

/-- Element-wise zip: length mismatch decides strongly; element results
    sequence with weakness propagation (Rust `SOrd::try_zip`). -/
def zipWithM {ε α : Type} (f : α → α → Except ε SOrd) (xs ys : Array α) :
    Except ε SOrd := do
  if xs.size < ys.size then
    return lt' true
  if xs.size > ys.size then
    return gt' true
  let mut weak := false
  for (a, b) in xs.zip ys do
    let r ← f a b
    match r with
    | ⟨true, .eq⟩ => pure ()
    | ⟨false, .eq⟩ => weak := true
    | _ => return if weak then ⟨false, r.ordering⟩ else r
  return eq' !weak

end SOrd

/-- Block-local address → class-index map (compile-side `MutConst::ctx`).
    Members of class `j` map to `j`; ctor addresses get offset indices
    starting at `classes.length`, advancing by the class's max ctor count. -/
structure KMutCtx where
  map : HashMap Address Nat := {}
  deriving Inhabited

namespace KMutCtx

def get? (ctx : KMutCtx) (a : Address) : Option Nat := ctx.map[a]?

def cnstCtors : KConst m → Array (KId m)
  | .indc (ctors := ctors) .. => ctors
  | _ => #[]

def fromIdClasses (classes : Array (Array (KId m × KConst m))) : KMutCtx :=
  Id.run do
    let mut map : HashMap Address Nat := {}
    let mut i := classes.size
    for h : j in [0:classes.size] do
      let mut maxCtors := 0
      for (id, c) in classes[j] do
        map := map.insert id.addr j
        let ctorIds := cnstCtors c
        maxCtors := max maxCtors ctorIds.size
        for hc : cidx in [0:ctorIds.size] do
          map := map.insert ctorIds[cidx].addr (i + cidx)
      i := i + maxCtors
    return ⟨map⟩

def fromIdPairs (pairs : Array (KId m × KConst m)) : KMutCtx :=
  fromIdClasses (pairs.map (#[·]))

end KMutCtx

/-- Ctor resolver for Indc-vs-Indc comparison (env lookup closure). -/
abbrev ResolveCtor (m : Mode) := KId m → Option (KConst m)

instance : Inhabited (KId m) := ⟨⟨default, Mode.F.mkDefault⟩⟩
instance : Inhabited (KConst m) :=
  ⟨.axio Mode.F.mkDefault Mode.F.mkDefault false 0 default⟩

/-- Structural universe comparison; `param` index is its identity.
    Variant order: zero < succ < max < imax < param. -/
partial def compareKUniv : KUniv m → KUniv m → SOrd
  | .zero _, .zero _ => .eq' true
  | .zero _, _ => .lt' true
  | _, .zero _ => .gt' true
  | .succ x _, .succ y _ => compareKUniv x y
  | .succ .., _ => .lt' true
  | _, .succ .. => .gt' true
  | .max xl xr _, .max yl yr _ =>
    (compareKUniv xl yl).andThen (compareKUniv xr yr)
  | .max .., _ => .lt' true
  | _, .max .. => .gt' true
  | .imax xl xr _, .imax yl yr _ =>
    (compareKUniv xl yl).andThen (compareKUniv xr yr)
  | .imax .., _ => .lt' true
  | _, .imax .. => .gt' true
  | .param xi _ _, .param yi _ _ => .ofOrdering (compare xi yi)

/-- Ctx-aware id comparison shared by `const` and `prj` heads: block-local
    hits compare weakly by class index; misses order strongly by address. -/
def compareCtxRef (ctx : KMutCtx) (x y : Address) : SOrd :=
  match ctx.get? x, ctx.get? y with
  | some nx, some ny => .weakOfOrdering (compare nx ny)
  | some _, none => .lt' true
  | none, some _ => .gt' true
  | none, none => .ofOrdering (Address.cmpBytes x y)

/-- Structural expression comparison for canonical ordering: alpha-blind
    through binders, ctx-aware for block-local refs. FVars must not appear
    (closed egressed expressions only). Variant order:
    var < sort < const < app < lam < all < letE < nat < str < prj. -/
partial def compareKExpr (ctx : KMutCtx) (x y : KExpr m) :
    Except (TcError m) SOrd := do
  if x.hasFVars || y.hasFVars then
    throw .unexpectedFVarInComparator
  if x.addr == y.addr then
    return .eq' true
  match x, y with
  | .fvar .., _ | _, .fvar .. => throw .unexpectedFVarInComparator
  | .var xi _ _, .var yi _ _ => return .ofOrdering (compare xi yi)
  | .var .., _ => return .lt' true
  | _, .var .. => return .gt' true
  | .sort xu _, .sort yu _ => return compareKUniv xu yu
  | .sort .., _ => return .lt' true
  | _, .sort .. => return .gt' true
  | .const xid xls _, .const yid yls _ =>
    let us ← SOrd.zipWithM (fun a b => pure (compareKUniv a b)) xls yls
    if us.ordering != .eq then
      return us
    if xid.addr == yid.addr then
      return .eq' true
    return compareCtxRef ctx xid.addr yid.addr
  | .const .., _ => return .lt' true
  | _, .const .. => return .gt' true
  | .app xl xr _, .app yl yr _ =>
    return (← compareKExpr ctx xl yl).andThen (← compareKExpr ctx xr yr)
  | .app .., _ => return .lt' true
  | _, .app .. => return .gt' true
  | .lam _ _ xt xb _, .lam _ _ yt yb _ =>
    return (← compareKExpr ctx xt yt).andThen (← compareKExpr ctx xb yb)
  | .lam .., _ => return .lt' true
  | _, .lam .. => return .gt' true
  | .all _ _ xt xb _, .all _ _ yt yb _ =>
    return (← compareKExpr ctx xt yt).andThen (← compareKExpr ctx xb yb)
  | .all .., _ => return .lt' true
  | _, .all .. => return .gt' true
  | .letE _ xt xv xb _ _, .letE _ yt yv yb _ _ =>
    SOrd.zipWithM (compareKExpr ctx) #[xt, xv, xb] #[yt, yv, yb]
  | .letE .., _ => return .lt' true
  | _, .letE .. => return .gt' true
  | .nat xv _ _, .nat yv _ _ => return .ofOrdering (compare xv yv)
  | .nat .., _ => return .lt' true
  | _, .nat .. => return .gt' true
  | .str xv _ _, .str yv _ _ => return .ofOrdering (compare xv yv)
  | .str .., _ => return .lt' true
  | _, .str .. => return .gt' true
  | .prj xid xi xb _, .prj yid yi yb _ =>
    let tn := compareCtxRef ctx xid.addr yid.addr
    return (tn.andThen (.ofOrdering (compare xi yi))).andThen
      (← compareKExpr ctx xb yb)

/-- Rule comparison: `(fields, rhs)`. -/
def compareKRecRule (ctx : KMutCtx) (x y : RecRule m) :
    Except (TcError m) SOrd := do
  return (SOrd.ofOrdering (compare x.fields y.fields)).andThen
    (← compareKExpr ctx x.rhs y.rhs)

def defKindOrd : Ix.DefKind → Nat
  | .defn => 0
  | .opaq => 1
  | .thm => 2

/-- Kind ordinal (compile-side `mut_const_kind`): Defn=0, Indc=1, Recr=2;
    Ctor/Axio/Quot get distinct slots for totality. -/
def kconstKindOrd : KConst m → Nat
  | .defn .. => 0
  | .indc .. => 1
  | .recr .. => 2
  | .ctor .. => 3
  | .axio .. => 4
  | .quot .. => 5

/-- Ctor payload: `(lvls, cidx, params, fields, ty)`. -/
def compareKCtor (ctx : KMutCtx) (x y : KConst m) :
    Except (TcError m) SOrd := do
  match x, y with
  | .ctor (lvls := xl) (cidx := xc) (params := xp) (fields := xf) (ty := xt) ..,
    .ctor (lvls := yl) (cidx := yc) (params := yp) (fields := yf) (ty := yt) .. =>
    return ((((SOrd.ofOrdering (compare xl yl)).andThen
      (.ofOrdering (compare xc yc))).andThen
      (.ofOrdering (compare xp yp))).andThen
      (.ofOrdering (compare xf yf))).andThen
      (← compareKExpr ctx xt yt)
  | _, _ => return .ofOrdering (compare (kconstKindOrd x) (kconstKindOrd y))

/-- Indc payload:
    `(is_unsafe, lvls, params, indices, |ctors|, ty, ctors[*])`. -/
def compareKIndc (ctx : KMutCtx) (resolveCtor : ResolveCtor m)
    (x y : KConst m) : Except (TcError m) SOrd := do
  match x, y with
  | .indc (lvls := xl) (params := xp) (indices := xi) (isUnsafe := xu)
      (ty := xt) (ctors := xc) ..,
    .indc (lvls := yl) (params := yp) (indices := yi) (isUnsafe := yu)
      (ty := yt) (ctors := yc) .. =>
    let head := ((((SOrd.ofOrdering (compare xu.toNat yu.toNat)).andThen
      (.ofOrdering (compare xl yl))).andThen
      (.ofOrdering (compare xp yp))).andThen
      (.ofOrdering (compare xi yi))).andThen
      (.ofOrdering (compare xc.size yc.size))
    let head := head.andThen (← compareKExpr ctx xt yt)
    let ctorsOrd ← SOrd.zipWithM (fun a b => do
        match resolveCtor a, resolveCtor b with
        | some ac, some bc => compareKCtor ctx ac bc
        | _, _ => pure (.ofOrdering (Address.cmpBytes a.addr b.addr)))
      xc yc
    return head.andThen ctorsOrd
  | _, _ => return .ofOrdering (compare (kconstKindOrd x) (kconstKindOrd y))

/-- Recr payload:
    `(lvls, params, indices, motives, minors, k, ty, rules[*])`. -/
def compareKRecr (ctx : KMutCtx) (x y : KConst m) :
    Except (TcError m) SOrd := do
  match x, y with
  | .recr (lvls := xl) (params := xp) (indices := xi) (motives := xm)
      (minors := xn) (k := xk) (ty := xt) (rules := xr) ..,
    .recr (lvls := yl) (params := yp) (indices := yi) (motives := ym)
      (minors := yn) (k := yk) (ty := yt) (rules := yr) .. =>
    let head := (((((SOrd.ofOrdering (compare xl yl)).andThen
      (.ofOrdering (compare xp yp))).andThen
      (.ofOrdering (compare xi yi))).andThen
      (.ofOrdering (compare xm ym))).andThen
      (.ofOrdering (compare xn yn))).andThen
      (.ofOrdering (compare xk.toNat yk.toNat))
    let head := head.andThen (← compareKExpr ctx xt yt)
    return head.andThen (← SOrd.zipWithM (compareKRecRule ctx) xr yr)
  | _, _ => return .ofOrdering (compare (kconstKindOrd x) (kconstKindOrd y))

/-- Defn payload: `(kind, lvls, ty, val)` — safety and hints intentionally
    NOT compared (matches compile-side). -/
def compareKDefn (ctx : KMutCtx) (x y : KConst m) :
    Except (TcError m) SOrd := do
  match x, y with
  | .defn (kind := xk) (lvls := xl) (ty := xt) (val := xv) ..,
    .defn (kind := yk) (lvls := yl) (ty := yt) (val := yv) .. =>
    let head := (SOrd.ofOrdering (compare (defKindOrd xk) (defKindOrd yk))).andThen
      (.ofOrdering (compare xl yl))
    let head := head.andThen (← compareKExpr ctx xt yt)
    return head.andThen (← compareKExpr ctx xv yv)
  | _, _ => return .ofOrdering (compare (kconstKindOrd x) (kconstKindOrd y))

/-- Full structural comparison of block-eligible constants. -/
def compareKConst (ctx : KMutCtx) (resolveCtor : ResolveCtor m)
    (x y : KConst m) : Except (TcError m) SOrd := do
  match x, y with
  | .defn .., .defn .. => compareKDefn ctx x y
  | .indc .., .indc .. => compareKIndc ctx resolveCtor x y
  | .recr .., .recr .. => compareKRecr ctx x y
  | _, _ => return .ofOrdering (compare (kconstKindOrd x) (kconstKindOrd y))

/-! ### sort_consts port (iterative partition refinement) -/

/-- Stable merge of two sorted arrays (left preferred on ties). -/
partial def mergeSorted (ctx : KMutCtx) (resolveCtor : ResolveCtor m)
    (left right : Array (KId m × KConst m)) :
    Except (TcError m) (Array (KId m × KConst m)) := do
  let mut result : Array (KId m × KConst m) :=
    Array.mkEmpty (left.size + right.size)
  let mut li := 0
  let mut ri := 0
  while li < left.size && ri < right.size do
    let cmp ← compareKConst ctx resolveCtor left[li]!.2 right[ri]!.2
    if cmp.ordering == .gt then
      result := result.push right[ri]!
      ri := ri + 1
    else
      result := result.push left[li]!
      li := li + 1
  result := result ++ left.extract li left.size
  result := result ++ right.extract ri right.size
  return result

/-- Merge-sort by structural comparison. -/
partial def sortByCompare (ctx : KMutCtx) (resolveCtor : ResolveCtor m)
    (items : Array (KId m × KConst m)) :
    Except (TcError m) (Array (KId m × KConst m)) := do
  if items.size ≤ 1 then
    return items
  let mid := items.size / 2
  let left ← sortByCompare ctx resolveCtor (items.extract 0 mid)
  let right ← sortByCompare ctx resolveCtor (items.extract mid items.size)
  mergeSorted ctx resolveCtor left right

/-- Group consecutive equal elements of a sorted array. -/
def groupConsecutive (ctx : KMutCtx) (resolveCtor : ResolveCtor m)
    (items : Array (KId m × KConst m)) :
    Except (TcError m) (Array (Array (KId m × KConst m))) := do
  let mut groups : Array (Array (KId m × KConst m)) := #[]
  let mut current : Array (KId m × KConst m) := #[]
  for item in items do
    match current.back? with
    | some last =>
      let so ← compareKConst ctx resolveCtor last.2 item.2
      if so.ordering == .eq then
        current := current.push item
      else
        groups := groups.push current
        current := #[item]
    | none => current := current.push item
  if !current.isEmpty then
    groups := groups.push current
  return groups

def classesEq (a b : Array (Array (KId m × KConst m))) : Bool := Id.run do
  if a.size != b.size then
    return false
  for i in [0:a.size] do
    let ca := a[i]!
    let cb := b[i]!
    if ca.size != cb.size then
      return false
    for j in [0:ca.size] do
      if ca[j]!.1.addr != cb[j]!.1.addr then
        return false
  return true

/-- Iterative partition refinement with a caller-provided deterministic
    seed/tiebreak key (compile-side seeds by `MutConst.name()`). -/
partial def sortKConstsWithSeedKey (resolveCtor : ResolveCtor m)
    (seedKey : KId m → KConst m → Address)
    (members : Array (KId m × KConst m)) :
    Except (TcError m) (Array (Array (KId m × KConst m))) := do
  if members.isEmpty then
    return #[]
  let seed := members.qsort fun a b =>
    match Address.cmpBytes (seedKey a.1 a.2) (seedKey b.1 b.2) with
    | .lt => true
    | .gt => false
    | .eq => Address.cmpBytes a.1.addr b.1.addr == .lt
  let mut classes : Array (Array (KId m × KConst m)) := #[seed]
  repeat
    let ctx := KMutCtx.fromIdClasses classes
    let mut newClasses : Array (Array (KId m × KConst m)) := #[]
    for cls in classes do
      if cls.size ≤ 1 then
        newClasses := newClasses.push cls
      else
        let sorted ← sortByCompare ctx resolveCtor cls
        newClasses := newClasses ++ (← groupConsecutive ctx resolveCtor sorted)
    if classesEq classes newClasses then
      return newClasses
    classes := newClasses
  return classes

/-- Refinement with the identity (address) seed key. -/
def sortKConsts (resolveCtor : ResolveCtor m)
    (members : Array (KId m × KConst m)) :
    Except (TcError m) (Array (Array (KId m × KConst m))) :=
  sortKConstsWithSeedKey resolveCtor (fun id _ => id.addr) members

/-- Compile-side seed: meta name hash when available, else the address. -/
def defaultSeedKey (id : KId m) : Address :=
  match Mode.get? id.name with
  | some name => name.getHash
  | none => id.addr

def validateByFullRefinement (blockAddr : Address)
    (resolveCtor : ResolveCtor m) (members : Array (KId m × KConst m)) :
    Except (TcError m) Unit := do
  let classes ← sortKConstsWithSeedKey resolveCtor
    (fun id _ => defaultSeedKey id) members
  if classes.size != members.size then
    let pos := (classes.findIdx? (·.size > 1)).getD 0
    throw (.nonCanonicalBlock blockAddr pos .eq)
  for i in [0:classes.size] do
    let cls := classes[i]!
    if cls.size != 1 || cls[0]!.1.addr != members[i]!.1.addr then
      throw (.nonCanonicalBlock blockAddr i .gt)

/-- Single-pass primary-block canonicity validation (see module doc). -/
def validateCanonicalBlockSinglePass (blockAddr : Address)
    (resolveCtor : ResolveCtor m) (members : Array (KId m × KConst m)) :
    Except (TcError m) Unit := do
  if members.size < 2 then
    return ()
  let ctx := KMutCtx.fromIdPairs members
  for i in [0:members.size - 1] do
    let so ← compareKConst ctx resolveCtor members[i]!.2 members[i+1]!.2
    match so.ordering, so.strong with
    | .lt, true => pure ()
    | .lt, false =>
      return (← validateByFullRefinement blockAddr resolveCtor members)
    | .eq, _ => throw (.nonCanonicalBlock blockAddr i .eq)
    | .gt, _ => throw (.nonCanonicalBlock blockAddr i .gt)

end Ix.Tc

end
end
