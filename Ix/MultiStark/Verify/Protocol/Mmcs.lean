module
public import Ix.MultiStark.Verify.Mmcs

/-! Binary, power-of-two MMCS relation. A proof supplies only row values and
the boundary digest sequence; dimensions, cap, and original query indices
are verifier inputs. The relation describes row equalities and each tree
layer, not an executable verifier's acceptance bit. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

abbrev MatrixRows := Array (Array (Array Field))

def rowDigest (values : Array Field) : Digest :=
  ⟨Ix.Ixby.Blake3.hash (values.flatMap (fun value => Codec.Wire.littleEndian 8 value.val)),
    Ix.Ixby.Blake3.hash_size _⟩

def branchDigest (left right : Digest) : Digest :=
  ⟨Ix.Ixby.Blake3.hash (left.bytes ++ right.bytes), Ix.Ixby.Blake3.hash_size _⟩

def MmcsGeometry (capHeight : Nat) (dimensions : Array Mmcs.Dimension) (cap : MerkleCap)
    (result : Nat × Nat) : Prop :=
  let height := dimensions.foldl (fun height dim => max height dim.logHeight) 0
  let effectiveCap := min capHeight height
  dimensions ≠ #[] ∧ (∀ dimension ∈ dimensions, dimension.logHeight ≤ 32) ∧
    cap.size = 2 ^ effectiveCap ∧ (∀ dimension ∈ dimensions, effectiveCap ≤ dimension.logHeight) ∧
    (height, effectiveCap) = result

def RowDimensions : List Mmcs.Dimension → List (Array Field) → Prop
  | [], [] => True
  | dimension :: dimensions, row :: rows => row.size = dimension.width ∧ RowDimensions dimensions rows
  | _, _ => False

def RowsWellFormed (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) : Prop :=
  ∀ query ∈ rows, query.size = dimensions.size ∧ RowDimensions dimensions.toList query.toList

def SameRows (rows : MatrixRows) (matrix : Nat) (expected : Array Field) (members : List Nat) : Prop :=
  ∀ member ∈ members, ∃ query, rows[member]? = some query ∧ query[matrix]? = some expected

def LayerRowsFrom (rows : MatrixRows) (height : Nat) (members : Array Nat) (lead : Array (Array Field)) :
    List Mmcs.Dimension → Nat → Array Field → Prop
  | [], _, result => #[] = result
  | dimension :: dimensions, matrix, result =>
    if dimension.logHeight = height then
      ∃ row rest, lead[matrix]? = some row ∧ SameRows rows matrix row members.toList ∧
        LayerRowsFrom rows height members lead dimensions (matrix + 1) rest ∧ row ++ rest = result
    else LayerRowsFrom rows height members lead dimensions (matrix + 1) result

def LayerRows (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) (height : Nat)
    (members : Array Nat) (result : Array Field) : Prop :=
  ∃ representative lead, members[0]? = some representative ∧ rows[representative]? = some lead ∧
    LayerRowsFrom rows height members lead dimensions.toList 0 result

def FreshLeaf (dimensions : Array Mmcs.Dimension) (rows : MatrixRows)
    (height index query : Nat) (before after : Array Mmcs.Node) : Prop :=
  ∃ row, LayerRows dimensions rows height #[query] row ∧
    before.push ⟨index, #[query], rowDigest row⟩ = after

def LeafStep (dimensions : Array Mmcs.Dimension) (rows : MatrixRows)
    (height index query : Nat) (before after : Array Mmcs.Node) : Prop :=
  index < 2 ^ height ∧
    match before.back? with
    | none => FreshLeaf dimensions rows height index query before after
    | some previous =>
      if previous.index = index then
        ∃ representative previousRows queryRows,
          previous.members[0]? = some representative ∧ rows[representative]? = some previousRows ∧
          rows[query]? = some queryRows ∧ previousRows = queryRows ∧ before = after
      else FreshLeaf dimensions rows height index query before after

def LeavesFrom (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) (height : Nat) :
    List (Nat × Nat) → Array Mmcs.Node → Array Mmcs.Node → Prop
  | [], before, after => before = after
  | (index, query) :: rest, before, after =>
    ∃ middle, LeafStep dimensions rows height index query before middle ∧
      LeavesFrom dimensions rows height rest middle after

/-- Stable ordering is a deterministic operation on the verifier's original
query vector; neither a sorting permutation nor indices are proof advice.
Duplicate positions are checked before the first representative is retained. -/
def Leaves (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) (height : Nat)
    (indices : Array Nat) (result : List Mmcs.Node) : Prop :=
  LeavesFrom dimensions rows height
    ((indices.zipIdx).toList.mergeSort (fun left right => left.1 ≤ right.1)) #[] result.toArray

def BoundaryParent (node : Mmcs.Node) (sibling : Digest) : Mmcs.Node :=
  ⟨node.index / 2, node.members,
    if node.index % 2 = 0 then branchDigest node.digest sibling else branchDigest sibling node.digest⟩

def PairedParent (left right : Mmcs.Node) : Mmcs.Node :=
  ⟨left.index / 2, left.members ++ right.members, branchDigest left.digest right.digest⟩

def ParentLayer (frontier : Array Digest) :
    List Mmcs.Node → Nat → List Mmcs.Node → Nat → Prop
  | [], cursor, result, finalCursor => ([], cursor) = (result, finalCursor)
  | [first], cursor, result, finalCursor =>
    ∃ sibling, frontier[cursor]? = some sibling ∧
      ([BoundaryParent first sibling], cursor + 1) = (result, finalCursor)
  | first :: second :: remaining, cursor, result, finalCursor =>
    if first.index / 2 = second.index / 2 then
      first.index % 2 = 0 ∧ second.index = first.index + 1 ∧
      ∃ more next, ParentLayer frontier remaining cursor more next ∧
        (PairedParent first second :: more, next) = (result, finalCursor)
    else
      ∃ sibling more next, frontier[cursor]? = some sibling ∧
        ParentLayer frontier (second :: remaining) (cursor + 1) more next ∧
        (BoundaryParent first sibling :: more, next) = (result, finalCursor)

def InjectedNodes (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) (height : Nat) :
    List Mmcs.Node → List Mmcs.Node → Prop
  | [], result => [] = result
  | node :: nodes, result =>
    ∃ row rest, LayerRows dimensions rows height node.members row ∧
      InjectedNodes dimensions rows height nodes rest ∧
      { node with digest := branchDigest node.digest (rowDigest row) } :: rest = result

def HasHeight (dimensions : Array Mmcs.Dimension) (height : Nat) : Prop :=
  ∃ dimension ∈ dimensions, dimension.logHeight = height

def Injection (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) (height : Nat)
    (nodes result : List Mmcs.Node) : Prop :=
  (¬HasHeight dimensions height ∧ nodes = result) ∨
    (HasHeight dimensions height ∧ InjectedNodes dimensions rows height nodes result)

def FrontierWalk (dimensions : Array Mmcs.Dimension) (rows : MatrixRows) (frontier : Array Digest) :
    Nat → Nat → List Mmcs.Node → Nat → List Mmcs.Node → Nat → Prop
  | 0, _, nodes, cursor, result, finalCursor => (nodes, cursor) = (result, finalCursor)
  | levels + 1, height, nodes, cursor, result, finalCursor =>
    ∃ parents nextCursor injected,
      ParentLayer frontier nodes cursor parents nextCursor ∧
      Injection dimensions rows (height - 1) parents injected ∧
      FrontierWalk dimensions rows frontier levels (height - 1) injected nextCursor result finalCursor

def CapMatched (cap : MerkleCap) (nodes : List Mmcs.Node) : Prop :=
  ∀ node ∈ nodes, cap[node.index]? = some node.digest

def MmcsAccepted (capHeight : Nat) (dimensions : Array Mmcs.Dimension) (cap : MerkleCap)
    (indices : Array Nat) (opening : BatchOpening) : Prop :=
  ∃ height effectiveCap leaves terminal,
    MmcsGeometry capHeight dimensions cap (height, effectiveCap) ∧
    opening.values.size = indices.size ∧ RowsWellFormed dimensions opening.values ∧
    Leaves dimensions opening.values height indices leaves ∧
    FrontierWalk dimensions opening.values opening.frontier (height - effectiveCap) height leaves 0
      terminal opening.frontier.size ∧ CapMatched cap terminal

end MultiStark.Verify.Protocol
