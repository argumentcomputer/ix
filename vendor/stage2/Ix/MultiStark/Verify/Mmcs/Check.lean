module
public import Ix.MultiStark.Verify.Mmcs.Basic

/-! A direct boundary-frontier walk for the current pruned multiproof.
Boundary digests are consumed bottom-up, parent indices ascending, then left
before right. Queried siblings are recomputed, never read from the proof.
All recursion is bounded by input lists or the admitted tree height. -/

public section
@[expose] section

namespace MultiStark.Verify.Mmcs

structure Node where
  index : Nat
  members : Array Nat
  digest : Digest
  deriving BEq, DecidableEq, Repr

def checkQueryRows : List Dimension → List (Array Field) → Except Error Unit
  | [], [] => .ok ()
  | dimension :: dimensions, row :: rows => do
    ensure (row.size == dimension.width) .rowWidth
    checkQueryRows dimensions rows
  | _, _ => .error .matrixCount

def checkRowList (dimensions : Array Dimension) : List (Array (Array Field)) → Except Error Unit
  | [] => .ok ()
  | query :: queries => do
    ensure (query.size == dimensions.size) .matrixCount
    checkQueryRows dimensions.toList query.toList
    checkRowList dimensions queries

def checkRows (dimensions : Array Dimension) (rows : Array (Array (Array Field))) : Except Error Unit :=
  checkRowList dimensions rows.toList

def checkSameRows (rows : Array (Array (Array Field))) (matrix : Nat) (expected : Array Field) :
    List Nat → Except Error Unit
  | [] => .ok ()
  | member :: members => do
    let query ← getAt rows member
    let row ← getAt query matrix
    ensure (row == expected) .groupRow
    checkSameRows rows matrix expected members

def layerRowsFrom (rows : Array (Array (Array Field))) (height : Nat) (members : Array Nat)
    (lead : Array (Array Field)) : List Dimension → Nat → Except Error (Array Field)
  | [], _ => .ok #[]
  | dimension :: dimensions, matrix =>
    if dimension.logHeight == height then do
      let row ← getAt lead matrix
      checkSameRows rows matrix row members.toList
      let rest ← layerRowsFrom rows height members lead dimensions (matrix + 1)
      return row ++ rest
    else layerRowsFrom rows height members lead dimensions (matrix + 1)

/-- Concatenate same-height rows in ORIGINAL matrix order. Every member of a
merged query group must report the same row for each newly injected matrix. -/
def layerRows (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (height : Nat) (members : Array Nat) : Except Error (Array Field) := do
  let representative ← getAt members 0
  let lead ← getAt rows representative
  layerRowsFrom rows height members lead dimensions.toList 0

def freshLeaf (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (height index query : Nat) (nodes : Array Node) : Except Error (Array Node) := do
  let row ← layerRows dimensions rows height #[query]
  return nodes.push ⟨index, #[query], hashRow row⟩

def leafStep (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (height index query : Nat) (nodes : Array Node) : Except Error (Array Node) := do
  ensure (decide (index < 2 ^ height)) .index
  match nodes.back? with
  | some previous =>
    if previous.index == index then do
      let representative ← getAt previous.members 0
      let previousRows ← getAt rows representative
      let queryRows ← getAt rows query
      ensure (previousRows == queryRows) .duplicateRow
      return nodes
    else freshLeaf dimensions rows height index query nodes
  | none => freshLeaf dimensions rows height index query nodes

def leavesFrom (dimensions : Array Dimension) (rows : Array (Array (Array Field))) (height : Nat) :
    List (Nat × Nat) → Array Node → Except Error (Array Node)
  | [], nodes => .ok nodes
  | (index, query) :: rest, nodes => do
    let nodes ← leafStep dimensions rows height index query nodes
    leavesFrom dimensions rows height rest nodes

def leaves (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (height : Nat) (indices : Array Nat) : Except Error (List Node) := do
  let ordered := (indices.zipIdx).toList.mergeSort (fun left right => left.1 ≤ right.1)
  return (← leavesFrom dimensions rows height ordered #[]).toList

def takeFrontier (frontier : Array Digest) (cursor : Nat) : Except Error Digest :=
  match frontier[cursor]? with | some digest => .ok digest | none => .error .frontier

/-- Merge one sorted-unique layer. No digest is manufactured for absent
advice: each unqueried sibling consumes exactly one boundary digest. -/
def parents (frontier : Array Digest) : List Node → Nat → Except Error (List Node × Nat)
  | [], cursor => .ok ([], cursor)
  | [first], cursor => do
    let sibling ← takeFrontier frontier cursor
    let digest := if first.index % 2 == 0 then compress first.digest sibling
      else compress sibling first.digest
    return ([⟨first.index / 2, first.members, digest⟩], cursor + 1)
  | first :: second :: remaining, cursor => do
    if first.index / 2 == second.index / 2 then
      ensure (first.index % 2 == 0 && second.index == first.index + 1) .internalShape
      let parent := Node.mk (first.index / 2) (first.members ++ second.members)
        (compress first.digest second.digest)
      let (more, finalCursor) ← parents frontier remaining cursor
      return (parent :: more, finalCursor)
    else
      let sibling ← takeFrontier frontier cursor
      let digest := if first.index % 2 == 0 then compress first.digest sibling
        else compress sibling first.digest
      let (more, finalCursor) ← parents frontier (second :: remaining) (cursor + 1)
      return (⟨first.index / 2, first.members, digest⟩ :: more, finalCursor)

def injectNodes (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (height : Nat) : List Node → Except Error (List Node)
  | [] => .ok []
  | node :: nodes => do
    let row ← layerRows dimensions rows height node.members
    let rest ← injectNodes dimensions rows height nodes
    return { node with digest := compress node.digest (hashRow row) } :: rest

def inject (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (height : Nat) (nodes : List Node) : Except Error (List Node) :=
  if dimensions.any (·.logHeight == height) then injectNodes dimensions rows height nodes else .ok nodes

def walk (dimensions : Array Dimension) (rows : Array (Array (Array Field)))
    (frontier : Array Digest) : Nat → Nat → List Node → Nat → Except Error (List Node × Nat)
  | 0, _, nodes, cursor => .ok (nodes, cursor)
  | levels + 1, height, nodes, cursor => do
    let (next, cursor) ← parents frontier nodes cursor
    let next ← inject dimensions rows (height - 1) next
    walk dimensions rows frontier levels (height - 1) next cursor

def checkCap (cap : MerkleCap) : List Node → Except Error Unit
  | [] => .ok ()
  | node :: nodes =>
    match cap[node.index]? with
    | none => .error .capMismatch
    | some expected => do
      ensure (node.digest == expected) .capMismatch
      checkCap cap nodes

def check (capHeight : Nat) (dimensions : Array Dimension) (cap : MerkleCap)
    (indices : Array Nat) (opening : BatchOpening) : Except Error Unit := do
  let (height, effectiveCap) ← geometry capHeight dimensions cap
  ensure (opening.values.size == indices.size) .queryCount
  checkRows dimensions opening.values
  let nodes ← leaves dimensions opening.values height indices
  let (nodes, cursor) ← walk dimensions opening.values opening.frontier
    (height - effectiveCap) height nodes 0
  ensure (cursor == opening.frontier.size) .frontier
  checkCap cap nodes

end MultiStark.Verify.Mmcs
