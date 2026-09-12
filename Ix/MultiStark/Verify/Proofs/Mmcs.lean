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

theorem takeFrontier_refines (frontier : Array Digest) (cursor : Nat) (digest : Digest) :
    Mmcs.takeFrontier frontier cursor = .ok digest ↔ frontier[cursor]? = some digest := by
  unfold Mmcs.takeFrontier
  cases frontier[cursor]? <;> simp

theorem parents_refines (frontier : Array Digest) (nodes : List Mmcs.Node) (cursor : Nat)
    (result : List Mmcs.Node) (finalCursor : Nat) :
    Mmcs.parents frontier nodes cursor = .ok (result, finalCursor) ↔
      Protocol.ParentLayer frontier nodes cursor result finalCursor := by
  cases nodes with
  | nil => simp [Mmcs.parents, Protocol.ParentLayer]
  | cons first remaining =>
    cases remaining with
    | nil =>
      simp only [Mmcs.parents, bind_ok_iff, pure_ok_iff, takeFrontier_refines,
        Protocol.ParentLayer, Protocol.BoundaryParent, beq_iff_eq, mmcs_compress_refines]
    | cons second rest =>
      by_cases paired : first.index / 2 = second.index / 2
      · simp only [Mmcs.parents, beq_iff_eq, paired, ↓reduceIte, bind_ok_iff,
          unit_exists_iff, ensure_ok_iff, Bool.and_eq_true, pure_ok_iff, Prod.exists,
          parents_refines frontier rest cursor, Protocol.ParentLayer, Protocol.PairedParent,
          mmcs_compress_refines, and_assoc]
      · simp only [Mmcs.parents, beq_iff_eq, paired, ↓reduceIte, bind_ok_iff,
          pure_ok_iff, Prod.exists, takeFrontier_refines,
          parents_refines frontier (second :: rest) (cursor + 1), Protocol.ParentLayer,
          Protocol.BoundaryParent, mmcs_compress_refines, exists_and_left]
termination_by structural nodes

theorem injectNodes_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) (height : Nat)
    (nodes result : List Mmcs.Node) :
    Mmcs.injectNodes dimensions rows height nodes = .ok result ↔
      Protocol.InjectedNodes dimensions rows height nodes result := by
  induction nodes generalizing result with
  | nil => simp [Mmcs.injectNodes, Protocol.InjectedNodes]
  | cons node nodes ih =>
    simp only [Mmcs.injectNodes, bind_ok_iff, pure_ok_iff, layerRows_refines, ih,
      Protocol.InjectedNodes, mmcs_hashRow_refines, mmcs_compress_refines, exists_and_left]

theorem hasHeight_refines (dimensions : Array Mmcs.Dimension) (height : Nat) :
    dimensions.any (·.logHeight == height) = true ↔ Protocol.HasHeight dimensions height := by
  simp only [Array.any_eq_true', beq_iff_eq, Protocol.HasHeight]

theorem inject_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) (height : Nat)
    (nodes result : List Mmcs.Node) :
    Mmcs.inject dimensions rows height nodes = .ok result ↔
      Protocol.Injection dimensions rows height nodes result := by
  unfold Mmcs.inject
  split
  next present =>
    have present := (hasHeight_refines dimensions height).mp present
    simpa only [Protocol.Injection, present, not_true_eq_false, false_and, true_and, false_or]
      using injectNodes_refines dimensions rows height nodes result
  next absent =>
    have absent : ¬Protocol.HasHeight dimensions height :=
      fun present => absent ((hasHeight_refines dimensions height).mpr present)
    simp [Protocol.Injection, absent]

theorem walk_refines (dimensions : Array Mmcs.Dimension) (rows : Protocol.MatrixRows) (frontier : Array Digest)
    (levels height : Nat) (nodes : List Mmcs.Node) (cursor : Nat) (result : List Mmcs.Node) (finalCursor : Nat) :
    Mmcs.walk dimensions rows frontier levels height nodes cursor = .ok (result, finalCursor) ↔
      Protocol.FrontierWalk dimensions rows frontier levels height nodes cursor result finalCursor := by
  induction levels generalizing height nodes cursor with
  | zero => simp [Mmcs.walk, Protocol.FrontierWalk]
  | succ levels ih =>
    simp only [Mmcs.walk, bind_ok_iff, Prod.exists, parents_refines, inject_refines, ih,
      Protocol.FrontierWalk, exists_and_left]

theorem checkCap_refines (cap : MerkleCap) (nodes : List Mmcs.Node) :
    Mmcs.checkCap cap nodes = .ok () ↔ Protocol.CapMatched cap nodes := by
  induction nodes with
  | nil => simp [Mmcs.checkCap, Protocol.CapMatched]
  | cons node nodes ih =>
    cases lookup : cap[node.index]? with
    | none => simp [Mmcs.checkCap, lookup, Protocol.CapMatched]
    | some expected =>
      simp only [Mmcs.checkCap, lookup, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
        digest_beq_iff_eq, ih, Protocol.CapMatched, List.mem_cons, forall_eq_or_imp,
        Option.some.injEq]
      simp only [eq_comm]

/-- The complete executable multiproof check is equivalent to the separate
row/frontier/cap relation. Both directions pin the consumed boundary cursor
to the full proof frontier; no trailing digest or queried cap is ignored. -/
theorem mmcs_check_refines (capHeight : Nat) (dimensions : Array Mmcs.Dimension) (cap : MerkleCap)
    (indices : Array Nat) (opening : BatchOpening) :
    Mmcs.check capHeight dimensions cap indices opening = .ok () ↔
      Protocol.MmcsAccepted capHeight dimensions cap indices opening := by
  simp only [Mmcs.check, bind_ok_iff, Prod.exists, mmcs_geometry_refines,
    unit_exists_iff, ensure_ok_iff, beq_iff_eq, checkRows_refines, leaves_refines,
    walk_refines, checkCap_refines, Protocol.MmcsAccepted]
  constructor
  · rintro ⟨height, effectiveCap, geometry, queryCount, rows, leaves, leafRelation,
      terminal, cursor, walked, rfl, caps⟩
    exact ⟨height, effectiveCap, leaves, terminal, geometry, queryCount, rows, leafRelation, walked, caps⟩
  · rintro ⟨height, effectiveCap, leaves, terminal, geometry, queryCount, rows, leafRelation, walked, caps⟩
    exact ⟨height, effectiveCap, geometry, queryCount, rows, leaves, leafRelation,
      terminal, opening.frontier.size, walked, rfl, caps⟩

end MultiStark.Verify.Proofs
