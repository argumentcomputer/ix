module
public import Ix.MultiStark.Verify.Protocol.Mmcs
public import Ix.MultiStark.Verify.Proofs.Basic

public section

namespace MultiStark.Verify.Proofs

theorem digest_beq_iff_eq (left right : Digest) : (left == right) = true ↔ left = right := by
  change instBEqDigest.beq left right = true ↔ _
  unfold instBEqDigest.beq
  split
  next a h b h' =>
    split
    next equal =>
      have same : a = b := beq_iff_eq.mp equal
      subst b
      simp only [iff_self]
    next unequal =>
      simp only [Bool.false_eq_true, Digest.mk.injEq, false_iff]
      intro same
      subst b
      exact unequal (by simp)
  next _ _ impossible =>
    exact False.elim (impossible left.bytes left.size right.bytes right.size rfl rfl)

theorem mmcs_hashRow_refines (values : Array Field) : Mmcs.hashRow values = Protocol.rowDigest values := rfl
theorem mmcs_compress_refines (left right : Digest) :
    Mmcs.compress left right = Protocol.branchDigest left right := rfl

theorem mmcs_getAt_refines {α : Type} (values : Array α) (index : Nat) (value : α) :
    Mmcs.getAt values index = .ok value ↔ values[index]? = some value := by
  unfold Mmcs.getAt
  cases values[index]? <;> simp

theorem mmcs_geometry_refines (capHeight : Nat) (dimensions : Array Mmcs.Dimension) (cap : MerkleCap)
    (result : Nat × Nat) :
    Mmcs.geometry capHeight dimensions cap = .ok result ↔ Protocol.MmcsGeometry capHeight dimensions cap result := by
  simp only [Mmcs.geometry, bind_ok_iff, unit_exists_iff, ensure_ok_iff, pure_ok_iff,
    Protocol.MmcsGeometry, Bool.not_eq_true', Array.isEmpty_eq_false_iff,
    Array.all_eq_true', decide_eq_true_eq, beq_iff_eq]
  rfl

theorem checkQueryRows_refines (dimensions : List Mmcs.Dimension) (rows : List (Array Field)) :
    Mmcs.checkQueryRows dimensions rows = .ok () ↔ Protocol.RowDimensions dimensions rows := by
  induction dimensions generalizing rows with
  | nil => cases rows <;> simp [Mmcs.checkQueryRows, Protocol.RowDimensions]
  | cons dimension dimensions ih =>
    cases rows with
    | nil => simp [Mmcs.checkQueryRows, Protocol.RowDimensions]
    | cons row rows =>
      simp only [Mmcs.checkQueryRows, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
        beq_iff_eq, ih, Protocol.RowDimensions]

theorem checkRowList_refines (dimensions : Array Mmcs.Dimension) (rows : List (Array (Array Field))) :
    Mmcs.checkRowList dimensions rows = .ok () ↔
      ∀ query ∈ rows, query.size = dimensions.size ∧ Protocol.RowDimensions dimensions.toList query.toList := by
  induction rows with
  | nil => simp [Mmcs.checkRowList]
  | cons query rows ih =>
    simp only [Mmcs.checkRowList, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      beq_iff_eq, checkQueryRows_refines, ih, List.mem_cons, forall_eq_or_imp, and_assoc]

theorem checkRows_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) :
    Mmcs.checkRows dimensions rows = .ok () ↔ Protocol.RowsWellFormed dimensions rows := by
  simpa only [Mmcs.checkRows, Protocol.RowsWellFormed, Array.mem_def] using checkRowList_refines dimensions rows.toList

theorem checkSameRows_refines (rows : Protocol.MatrixRows) (matrix : Nat) (expected : Array Field) (members : List Nat) :
    Mmcs.checkSameRows rows matrix expected members = .ok () ↔ Protocol.SameRows rows matrix expected members := by
  induction members with
  | nil => simp [Mmcs.checkSameRows, Protocol.SameRows]
  | cons member members ih =>
    simp only [Mmcs.checkSameRows, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      mmcs_getAt_refines, beq_iff_eq, ih, Protocol.SameRows, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨query, queryAt, row, rowAt, rfl, rest⟩
      exact ⟨⟨query, queryAt, rowAt⟩, rest⟩
    · rintro ⟨⟨query, queryAt, rowAt⟩, rest⟩
      exact ⟨query, queryAt, expected, rowAt, rfl, rest⟩

theorem layerRowsFrom_refines (rows : Protocol.MatrixRows) (height : Nat) (members : Array Nat)
    (lead : Array (Array Field)) (dimensions : List Mmcs.Dimension) (matrix : Nat) (result : Array Field) :
    Mmcs.layerRowsFrom rows height members lead dimensions matrix = .ok result ↔
      Protocol.LayerRowsFrom rows height members lead dimensions matrix result := by
  induction dimensions generalizing matrix result with
  | nil => simp [Mmcs.layerRowsFrom, Protocol.LayerRowsFrom]
  | cons dimension dimensions ih =>
    by_cases matchingHeight : dimension.logHeight = height
    · simp only [Mmcs.layerRowsFrom, beq_iff_eq, matchingHeight, ↓reduceIte, bind_ok_iff,
        unit_exists_iff, pure_ok_iff, mmcs_getAt_refines, checkSameRows_refines, ih,
        Protocol.LayerRowsFrom, exists_and_left]
    · simp only [Mmcs.layerRowsFrom, beq_iff_eq, matchingHeight, ↓reduceIte, ih, Protocol.LayerRowsFrom]

theorem layerRows_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) (height : Nat)
    (members : Array Nat) (result : Array Field) :
    Mmcs.layerRows dimensions rows height members = .ok result ↔ Protocol.LayerRows dimensions rows height members result := by
  simp only [Mmcs.layerRows, bind_ok_iff, mmcs_getAt_refines, layerRowsFrom_refines,
    Protocol.LayerRows, exists_and_left]

theorem freshLeaf_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows)
    (height index query : Nat) (before after : Array Mmcs.Node) :
    Mmcs.freshLeaf dimensions rows height index query before = .ok after ↔
      Protocol.FreshLeaf dimensions rows height index query before after := by
  simp only [Mmcs.freshLeaf, bind_ok_iff, pure_ok_iff, layerRows_refines,
    mmcs_hashRow_refines, Protocol.FreshLeaf]

theorem leafStep_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows)
    (height index query : Nat) (before after : Array Mmcs.Node) :
    Mmcs.leafStep dimensions rows height index query before = .ok after ↔
      Protocol.LeafStep dimensions rows height index query before after := by
  simp only [Mmcs.leafStep, bind_ok_iff, unit_exists_iff, ensure_ok_iff, decide_eq_true_eq,
    Protocol.LeafStep]
  cases before.back? with
  | none => simp only [freshLeaf_refines]
  | some previous =>
    by_cases same : previous.index = index
    · simp only [beq_iff_eq, same, ↓reduceIte, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
        pure_ok_iff, mmcs_getAt_refines, exists_and_left]
    · simp only [beq_iff_eq, same, ↓reduceIte, freshLeaf_refines]

theorem leavesFrom_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) (height : Nat)
    (ordered : List (Nat × Nat)) (before after : Array Mmcs.Node) :
    Mmcs.leavesFrom dimensions rows height ordered before = .ok after ↔
      Protocol.LeavesFrom dimensions rows height ordered before after := by
  induction ordered generalizing before with
  | nil => simp [Mmcs.leavesFrom, Protocol.LeavesFrom]
  | cons pair rest ih =>
    cases pair
    simp only [Mmcs.leavesFrom, bind_ok_iff, leafStep_refines, ih, Protocol.LeavesFrom]

theorem leaves_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) (height : Nat)
    (indices : Array Nat) (result : List Mmcs.Node) :
    Mmcs.leaves dimensions rows height indices = .ok result ↔ Protocol.Leaves dimensions rows height indices result := by
  simp only [Mmcs.leaves, bind_ok_iff, pure_ok_iff, leavesFrom_refines, Protocol.Leaves]
  constructor
  · rintro ⟨nodes, steps, equal⟩
    cases equal
    simpa using steps
  · intro steps
    exact ⟨result.toArray, steps, by simp⟩

end MultiStark.Verify.Proofs
