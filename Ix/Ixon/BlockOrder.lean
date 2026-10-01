/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0

Canonical comparison and refinement follow crates/kernel/src/canonical_check.rs
and crates/common/src/strong_ordering.rs at Ix revision
11aa5649700b371e1c65dcb86157999839fe7e5e. This adapter compares physical Ixon
references directly; it does not import the old Ix.Tc representation.
-/

import Ix.Ixon.Projection
import Ix.Ixon.ReduceUniverse

/-! Canonical mutual-block order, outside the hash-free kernel.

Full partition refinement uses only the ordering component of the production
comparator. It avoids the native hash-equality shortcut and the strong-order
fast path. Lists compare lexicographically (including unequal lengths).
Projection addresses are computed by the pure writer/hash path. Universes
are rebuilt once through the same simplifying constructors as host ingress.
Sharing is followed only to earlier entries, without constructing another
expanded expression tree. Literal comparison uses values, not blob addresses.

A block whose members are all recursors is checked in motive order instead
(`checkMotives`): member `j` eliminates motive `j` and declares one motive per
member. That is the order the compiler stores a recursor block in (`T.rec`,
`T.rec_1`, …; for a mutual block, its members' order) and the order in which
the Ixon reader regroups a block's recursors (`ConLecheReader.buildIndex`
reads each recursor's motive off its type), and it is not always the
structural order (a nested block's auxiliary recursors, or a mutual block's
recursors whose types compare otherwise). Inductive, definition and mixed
blocks keep the structural check.

This is an ordering check, not a second typechecker or a complete validator
of unused tables: the final kernel admission still checks the entire input.
-/

namespace Ix.Ixon.BlockOrder

open Kernel hiding Expr  -- `Expr` is Ixon's here (the vendored checker's is `Ix.Kernel.Expr`)
open _root_.Ixon (Univ Expr MutConst)

abbrev Classes := List (List Nat)
abbrev LocalContext := List (Address × Nat)

inductive Resource where
  | comparison
  | refinement
  deriving Repr, DecidableEq

inductive Error where
  | exhausted (resource : Resource)
  | malformed (reason : String)
  | nonCanonical (owner : Address) (classes : Classes)
  /-- a recursor block's member `position` does not eliminate motive
  `position` of a block with one motive per member (`motive`: the motive its
  type eliminates, if it has the recursor shape) -/
  | motiveOrder (owner : Address) (position : Nat) (motive : Option Nat)
  | projection (reason : Projection.Error)
  | admission (reason : Admission.Error)
  deriving Repr, DecidableEq

/-- Comparison bounds recursive expression/sharing descent; refinement
bounds complete passes, including the final pass witnessing a fixed point.
Neither parameter is a wall-clock or total allocation bound. -/
structure Limits where
  comparison : Nat := 256
  refinement : Nat := 256
  deriving Repr

structure Entry where
  address : Address
  constructors : List Address
  value : MutConst

structure Block where
  source : _root_.Ixon.Constant
  entries : Array Entry
  universes : Array Univ
  blobs : Ingress.Blobs

def projectionAddress (layout : Egress.ProjectionLayout) (reference : ConstRef Address) :
    Except Error Address := do
  if reference.block.hash.size != 32 then
    throw (.projection (.ownerWidth reference.block))
  let record ← (Egress.writeProjection layout reference).mapError
    (fun error => .projection (.projection error))
  return Projection.address record

def prepareEntry (owner : Address) (index : Nat) (member : MutConst) : Except Error Entry := do
  match member with
  | .defn _ => return ⟨← projectionAddress .definition (.member owner index), [], member⟩
  | .recr _ => return ⟨← projectionAddress .recursor (.member owner index), [], member⟩
  | .indc value =>
    let address ← projectionAddress .inductive (.member owner index)
    let constructors ← value.ctors.toList.zipIdx.mapM fun (_, ctor) =>
      projectionAddress .constructor (.ctor owner index ctor)
    return ⟨address, constructors, member⟩

def prepare (owner : Address) (source : _root_.Ixon.Constant) (blobs : Ingress.Blobs) :
    Except Error Block := do
  let .muts members := source.info | throw (.malformed "expected a mutual block")
  let entries ← members.toList.zipIdx.mapM fun (member, index) => prepareEntry owner index member
  return ⟨source, entries.toArray, source.univs.map _root_.Ixon.reduceUniv, blobs⟩

def required (reason : String) : Option α → Except Error α
  | some value => .ok value
  | none => .error (.malformed reason)

def entry (block : Block) (index : Nat) : Except Error Entry :=
  required "member index outside block" block.entries[index]?

/-- The prepend implements the native map's last-insertion-wins behavior.
Constructor slots start after the classes and advance by the maximum number
of constructors in each class, not by the sum over equivalent members. -/
def localContext (block : Block) (classes : Classes) : Except Error LocalContext := do
  let mut result := []
  let mut offset := classes.length
  for (members, classIndex) in classes.zipIdx do
    let mut maxConstructors := 0
    for index in members do
      let item ← entry block index
      result := (item.address, classIndex) :: result
      maxConstructors := max maxConstructors item.constructors.length
      for (address, ctor) in item.constructors.zipIdx do
        result := (address, offset + ctor) :: result
    offset := offset + maxConstructors
  return result

def compareAddress (ctx : LocalContext) (left right : Address) : Ordering :=
  match Ingress.lookup ctx left, Ingress.lookup ctx right with
  | some x, some y => compare x y
  | some _, none => .lt
  | none, some _ => .gt
  | none, none => Address.cmpBytes left right

def thenM (first : Ordering) (next : Unit → Except Error Ordering) : Except Error Ordering :=
  if first == .eq then next () else .ok first

/-- True lexicographic comparison: length decides only after an equal prefix. -/
def compareListM {α : Type} (cmp : α → α → Except Error Ordering) :
    List α → List α → Except Error Ordering
  | [], [] => .ok .eq
  | [], _ :: _ => .ok .lt
  | _ :: _, [] => .ok .gt
  | x :: xs, y :: ys => do
    thenM (← cmp x y) fun _ => compareListM cmp xs ys

def compareUniverse : Univ → Univ → Ordering
  | .zero, .zero => .eq
  | .zero, _ => .lt
  | _, .zero => .gt
  | .succ x, .succ y => compareUniverse x y
  | .succ _, _ => .lt
  | _, .succ _ => .gt
  | .max xl xr, .max yl yr =>
    let first := compareUniverse xl yl
    if first == .eq then compareUniverse xr yr else first
  | .max .., _ => .lt
  | _, .max .. => .gt
  | .imax xl xr, .imax yl yr =>
    let first := compareUniverse xl yl
    if first == .eq then compareUniverse xr yr else first
  | .imax .., _ => .lt
  | _, .imax .. => .gt
  | .var x, .var y => compare x y

def universeAt (block : Block) (index : UInt64) : Except Error Univ :=
  required "universe index outside table" block.universes[index.toNat]?

def referenceAt (block : Block) (index : UInt64) : Except Error Address :=
  required "reference index outside table" block.source.refs[index.toNat]?

def recursiveAt (block : Block) (index : UInt64) : Except Error Address := do
  return (← entry block index.toNat).address

def blobAt (block : Block) (index : UInt64) : Except Error ByteArray := do
  let key ← referenceAt block index
  required "literal blob is absent" (Ingress.lookup block.blobs key)

def sharingAt (block : Block) (limit : Nat) (index : UInt64) : Except Error Expr :=
  if index.toNat < limit then
    required "sharing index outside table" block.source.sharing[index.toNat]?
  else .error (.malformed "sharing reference is not earlier than its use")

def compareInstance (block : Block) (ctx : LocalContext)
    (left right : Address) (xs ys : Array UInt64) : Except Error Ordering := do
  let levels ← compareListM (fun x y => do
    return compareUniverse (← universeAt block x) (← universeAt block y)) xs.toList ys.toList
  thenM levels fun _ => pure (compareAddress ctx left right)

def exprKind : Expr → Nat
  | .var _ => 0
  | .sort _ => 1
  | .ref .. | .recur .. => 2
  | .app .. => 3
  | .lam .. => 4
  | .all .. => 5
  | .letE .. => 6
  | .nat _ => 7
  | .str _ => 8
  | .prj .. => 9
  | .share _ => 10 -- eliminated before comparing variants

/-- Binder modes and the let nondependency bit do not affect canonical
ordering. Physical ref aliases are retained, and recursive slots resolve to
the computed projection keys rather than logical ConstRef values. -/
def compareExpr (block : Block) (ctx : LocalContext) :
    Nat → Nat → Expr → Nat → Expr → Except Error Ordering
  | 0, _, _, _, _ => .error (.exhausted .comparison)
  | fuel + 1, leftLimit, .share i, rightLimit, right => do
    let left ← sharingAt block leftLimit i
    compareExpr block ctx fuel i.toNat left rightLimit right
  | fuel + 1, leftLimit, left, rightLimit, .share i => do
    let right ← sharingAt block rightLimit i
    compareExpr block ctx fuel leftLimit left i.toNat right
  | fuel + 1, leftLimit, left, rightLimit, right => do
    match left, right with
    | .var x, .var y => return compare x y
    | .sort x, .sort y => return compareUniverse (← universeAt block x) (← universeAt block y)
    | .ref x xs, .ref y ys =>
      compareInstance block ctx (← referenceAt block x) (← referenceAt block y) xs ys
    | .ref x xs, .recur y ys =>
      compareInstance block ctx (← referenceAt block x) (← recursiveAt block y) xs ys
    | .recur x xs, .ref y ys =>
      compareInstance block ctx (← recursiveAt block x) (← referenceAt block y) xs ys
    | .recur x xs, .recur y ys =>
      compareInstance block ctx (← recursiveAt block x) (← recursiveAt block y) xs ys
    | .app xl xr, .app yl yr
    | .lam _ xl xr, .lam _ yl yr
    | .all _ _ xl xr, .all _ _ yl yr =>
      thenM (← compareExpr block ctx fuel leftLimit xl rightLimit yl) fun _ =>
        compareExpr block ctx fuel leftLimit xr rightLimit yr
    | .letE _ xt xv xb, .letE _ yt yv yb =>
      thenM (← compareExpr block ctx fuel leftLimit xt rightLimit yt) fun _ => do
        thenM (← compareExpr block ctx fuel leftLimit xv rightLimit yv) fun _ =>
          compareExpr block ctx fuel leftLimit xb rightLimit yb
    | .nat x, .nat y => return compare (Ingress.natural (← blobAt block x)) (Ingress.natural (← blobAt block y))
    | .str x, .str y =>
      let x ← required "literal is not UTF-8" (String.fromUTF8? (← blobAt block x))
      let y ← required "literal is not UTF-8" (String.fromUTF8? (← blobAt block y))
      return compare x y
    | .prj xt xi xv, .prj yt yi yv =>
      thenM (compareAddress ctx (← referenceAt block xt) (← referenceAt block yt)) fun _ =>
        thenM (compare xi yi) fun _ => compareExpr block ctx fuel leftLimit xv rightLimit yv
    | _, _ => return compare (exprKind left) (exprKind right)

def compareRoot (block : Block) (ctx : LocalContext) (fuel : Nat) (left right : Expr) :
    Except Error Ordering :=
  compareExpr block ctx fuel block.source.sharing.size left block.source.sharing.size right

def compareConstructor (block : Block) (ctx : LocalContext) (fuel : Nat)
    (left right : _root_.Ixon.Constructor) : Except Error Ordering :=
  thenM (compare [left.lvls, left.cidx, left.params, left.fields]
    [right.lvls, right.cidx, right.params, right.fields]) fun _ =>
    compareRoot block ctx fuel left.typ right.typ

def compareRule (block : Block) (ctx : LocalContext) (fuel : Nat)
    (left right : _root_.Ixon.RecursorRule) : Except Error Ordering :=
  thenM (compare left.fields right.fields) fun _ => compareRoot block ctx fuel left.rhs right.rhs

def definitionKind : DefKind → Nat
  | .defn => 0
  | .opaq => 1
  | .thm => 2

def memberKind : MutConst → Nat
  | .defn _ => 0
  | .indc _ => 1
  | .recr _ => 2

def compareMember (block : Block) (ctx : LocalContext) (fuel : Nat) :
    MutConst → MutConst → Except Error Ordering
  | .defn x, .defn y =>
    thenM (compare [definitionKind x.kind, x.lvls.toNat]
      [definitionKind y.kind, y.lvls.toNat]) fun _ => do
      thenM (← compareRoot block ctx fuel x.typ y.typ) fun _ =>
        compareRoot block ctx fuel x.value y.value
  | .indc x, .indc y =>
    thenM (compare [x.isUnsafe.toNat, x.lvls.toNat, x.params.toNat, x.indices.toNat, x.ctors.size]
      [y.isUnsafe.toNat, y.lvls.toNat, y.params.toNat, y.indices.toNat, y.ctors.size]) fun _ => do
      thenM (← compareRoot block ctx fuel x.typ y.typ) fun _ =>
        compareListM (compareConstructor block ctx fuel) x.ctors.toList y.ctors.toList
  | .recr x, .recr y =>
    thenM (compare [x.lvls.toNat, x.params.toNat, x.indices.toNat, x.motives.toNat, x.minors.toNat, x.k.toNat]
      [y.lvls.toNat, y.params.toNat, y.indices.toNat, y.motives.toNat, y.minors.toNat, y.k.toNat]) fun _ => do
      thenM (← compareRoot block ctx fuel x.typ y.typ) fun _ =>
        compareListM (compareRule block ctx fuel) x.rules.toList y.rules.toList
  | x, y => .ok (compare (memberKind x) (memberKind y))

def compareIndex (block : Block) (ctx : LocalContext) (fuel : Nat) (left right : Nat) :
    Except Error Ordering := do
  compareMember block ctx fuel (← entry block left).value (← entry block right).value

/-- Stable merge, preferring the left input on ties. -/
def mergeM (cmp : Nat → Nat → Except Error Ordering) :
    List Nat → List Nat → Except Error (List Nat)
  | [], ys => .ok ys
  | xs, [] => .ok xs
  | x :: xs, y :: ys => do
    if (← cmp x y) == .gt then
      return y :: (← mergeM cmp (x :: xs) ys)
    else return x :: (← mergeM cmp xs (y :: ys))
termination_by xs ys => xs.length + ys.length

/-- The size-derived budget bounds splitting depth. Unlike the old checker,
running out of any explicit fuel never returns an unfinished result. -/
def sortFuel (cmp : Nat → Nat → Except Error Ordering) :
    Nat → List Nat → Except Error (List Nat)
  | _, [] => .ok []
  | _, [x] => .ok [x]
  | 0, _ :: _ :: _ => .error (.malformed "internal merge-sort bound")
  | fuel + 1, xs => do
    let half := xs.length / 2
    let left ← sortFuel cmp fuel (xs.take half)
    let right ← sortFuel cmp fuel (xs.drop half)
    mergeM cmp left right

def sortM (cmp : Nat → Nat → Except Error Ordering) (xs : List Nat) : Except Error (List Nat) :=
  sortFuel cmp xs.length xs

/-- Compare adjacent elements, retaining the order inside each equal class. -/
def groupM (cmp : Nat → Nat → Except Error Ordering) (last : Nat) (reversed : List Nat) :
    List Nat → Except Error Classes
  | [] => .ok [reversed.reverse]
  | x :: xs => do
    if (← cmp last x) == .eq then groupM cmp x (x :: reversed) xs
    else return reversed.reverse :: (← groupM cmp x [x] xs)

def groupSorted (cmp : Nat → Nat → Except Error Ordering) : List Nat → Except Error Classes
  | [] => .ok []
  | x :: xs => groupM cmp x [x] xs

def refineStep (block : Block) (comparison : Nat) (classes : Classes) : Except Error Classes := do
  let ctx ← localContext block classes
  let cmp := compareIndex block ctx comparison
  let groups ← classes.mapM fun members => do
    match members with
    | [] => throw (.malformed "empty refinement class")
    | [_] => pure [members]
    | _ => groupSorted cmp (← sortM cmp members)
  return groups.flatten

/-- A result is returned only after observing an unchanged complete pass. -/
def refine (block : Block) (comparison : Nat) : Nat → Classes → Except Error Classes
  | 0, _ => .error (.exhausted .refinement)
  | fuel + 1, classes => do
    let next ← refineStep block comparison classes
    if next = classes then return next
    refine block comparison fuel next

def seed (block : Block) : Except Error Classes := do
  if block.entries.isEmpty then return []
  let indices ← sortM (fun x y => do
    return Address.cmpBytes (← entry block x).address (← entry block y).address)
    (List.range block.entries.size)
  return [indices]

def canonicalClasses (limits : Limits) (block : Block) : Except Error Classes := do
  refine block limits.comparison limits.refinement (← seed block)

def orderedSingletons (size : Nat) : Classes := (List.range size).map fun index => [index]

def checkBlock (limits : Limits) (owner : Address) (source : _root_.Ixon.Constant)
    (blobs : Ingress.Blobs) : Except Error Unit := do
  let block ← prepare owner source blobs
  let classes ← canonicalClasses limits block
  if classes = orderedSingletons block.entries.size then return ()
  throw (.nonCanonical owner classes)

/-! ## Recursor blocks: motive order -/

def isRecursor : MutConst → Bool
  | .recr _ => true
  | _ => false

/-- The motive a recursor eliminates, read off its type exactly as the Ixon
reader does (the first component of `ConLecheReader.analyseRecursor`): after
the parameters, motives, minors, indices and the major premise, the head of
the result is the bound variable of one of the motives. -/
def recursorMotive (source : _root_.Ixon.Constant) (r : _root_.Ixon.Recursor) : Option Nat := do
  let nP := r.params.toNat
  let nM := r.motives.toNat
  let depth := nP + nM + r.minors.toNat + r.indices.toNat + 1
  let (_, body) ← ConLecheReader.stripAll source depth r.typ
  let .var k := ConLecheReader.appHead source ConLecheReader.spineFuel body | none
  let pos := depth - 1 - k.toNat
  guard (k.toNat < depth && nP ≤ pos && pos < nP + nM)
  pure (pos - nP)

/-- The members from `position` on are recursors in motive order: the one at
`position` eliminates motive `position`, of `size` motives. -/
def checkMotives (owner : Address) (source : _root_.Ixon.Constant) (size : Nat) :
    Nat → List MutConst → Except Error Unit
  | _, [] => .ok ()
  | position, member :: rest => do
    match member with
    | .recr r =>
      let motive := recursorMotive source r
      unless r.motives.toNat == size && motive == some position do
        throw (.motiveOrder owner position motive)
    | _ => throw (.malformed "expected a recursor")
    checkMotives owner source size (position + 1) rest

/-- One record's order check: a recursor block in motive order, any other
`muts` block in canonical structural order (`checkBlock`), nothing else. -/
def checkRecord (limits : Limits) (blobs : Ingress.Blobs) (owner : Address)
    (source : _root_.Ixon.Constant) : Except Error Unit :=
  match source.info with
  | .muts members =>
    if members.all isRecursor then checkMotives owner source members.size 0 members.toList
    else checkBlock limits owner source blobs
  | _ => .ok ()

def checkConstants (limits : Limits) (blobs : Ingress.Blobs) :
    Ingress.Constants → Except Error Unit
  | [] => .ok ()
  | (owner, source) :: rest => do
    checkRecord limits blobs owner source
    checkConstants limits blobs rest

/-- Failures of the certified entry: byte admission, reconstruction and
order (`Error`), or the checker (`ConLecheAdmission.Error`). -/
inductive CheckError where
  | order (error : Error)
  | checker (error : ConLecheAdmission.Error)

/-- **The certified entry with canonical block order**: byte spelling,
computed projections, canonical block order (recursor blocks in motive
order), and con-leche's verified
checker behind the Ixon reader are all executed here. No host ordering
verdict is input. -/
def checkBytes (maxProjections : Nat) (limits : Admission.Limits) (orderLimits : Limits)
    (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except CheckError Ix.Kernel.Env := do
  (Admission.preflight limits records blobs).mapError (fun error => .order (.admission error))
  (Admission.uniqueKeys records blobs).mapError (fun error => .order (.admission error))
  let constants ← (Admission.decodeRecords limits records).mapError (fun error => .order (.admission error))
  let expanded ← (Projection.reconstruct maxProjections constants).mapError
    (fun error => .order (.projection error))
  (checkConstants orderLimits blobs constants).mapError .order
  (ConLecheAdmission.checkConstants expanded blobs hint).mapError .checker

end Ix.Ixon.BlockOrder
