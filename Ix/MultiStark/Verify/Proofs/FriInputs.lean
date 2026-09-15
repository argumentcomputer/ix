module
public import Ix.MultiStark.Verify.Protocol.FriInputs
public import Ix.MultiStark.Verify.Proofs.FriFold
public import Ix.MultiStark.Verify.Proofs.Mmcs

public section

namespace MultiStark.Verify.Proofs

theorem fri_getAt_refines {α : Type} (values : Array α) (index : Nat) (value : α) :
    Fri.getAt values index = .ok value ↔ values[index]? = some value := by
  unfold Fri.getAt
  cases values[index]? <;> simp

theorem authenticateInputBatches_refines (params : Parameters) (challenges : Fri.Challenges)
    (openings : Array BatchOpening) (rounds : List Pcs.Round) (batch : Nat) :
    Fri.authenticateInputBatches params challenges openings rounds batch = .ok () ↔
      Protocol.AuthenticatedBatches params challenges openings rounds batch := by
  induction rounds generalizing batch with
  | nil => simp [Fri.authenticateInputBatches, Protocol.AuthenticatedBatches]
  | cons round rounds ih =>
    simp only [Fri.authenticateInputBatches, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      Bool.not_eq_true', Array.isEmpty_eq_false_iff, decide_eq_true_eq, fri_getAt_refines,
      mapError_ok_iff, mmcs_check_refines, ih, Protocol.AuthenticatedBatches]
    rfl

theorem authenticateInputs_refines (params : Parameters) (challenges : Fri.Challenges)
    (rounds : Array Pcs.Round) (openings : Array BatchOpening) :
    Fri.authenticateInputs params challenges rounds openings = .ok () ↔
      Protocol.InputAuthenticated params challenges rounds openings := by
  simp only [Fri.authenticateInputs, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    authenticateInputBatches_refines, Protocol.InputAuthenticated, and_assoc]

theorem queryPoint_refines (index logGlobal logHeight : Nat) (result : Ext) :
    Fri.queryPoint index logGlobal logHeight = .ok result ↔
      Protocol.InputQueryPoint index logGlobal logHeight result := by
  simp only [Fri.queryPoint, bind_ok_iff, unit_exists_iff, ensure_ok_iff, Bool.and_eq_true,
    decide_eq_true_eq, mapError_ok_iff, twoAdicGenerator_refines, pure_ok_iff,
    reverseBits_refines, Protocol.InputQueryPoint, and_assoc]

theorem coordinateStep_refines (alpha reciprocal power value : Ext) (atX : Field) (atZ : Ext) :
    Fri.coordinateStep alpha reciprocal (power, value) (atX, atZ) =
      (power.mul alpha, value.add (power.mul ((atZ.sub (Arithmetic.embed atX)).mul reciprocal))) := rfl

theorem reduceCoordinatePairs_refines (alpha reciprocal : Ext) (coordinates : List (Field × Ext)) (state : Ext × Ext) :
    Fri.reduceCoordinatePairs alpha reciprocal coordinates state =
      Protocol.CoordinateSum alpha reciprocal coordinates state := by
  induction coordinates generalizing state with
  | nil => rfl
  | cons coordinate coordinates ih =>
    cases coordinate with
    | mk atX atZ =>
      cases state with
      | mk power value => exact ih (Fri.coordinateStep alpha reciprocal (power, value) (atX, atZ))

theorem reduceCoordinates_refines (alpha reciprocal : Ext) (row : List Field) (opened : List Ext)
    (power value : Ext) (result : Ext × Ext) :
    Fri.reduceCoordinates alpha reciprocal row opened power value = .ok result ↔
      Protocol.CoordinateReduction alpha reciprocal row opened power value result := by
  simp only [Fri.reduceCoordinates, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
    beq_iff_eq, pure_ok_iff, reduceCoordinatePairs_refines, Protocol.CoordinateReduction]

theorem reducePoints_refines (alpha x : Ext) (width : Nat) (row : Array Field)
    (points : List Pcs.PointOpening) (power value : Ext) (result : Ext × Ext) :
    Fri.reducePoints alpha x width row points power value = .ok result ↔
      Protocol.PointReduction alpha x width row points power value result := by
  induction points generalizing power value with
  | nil => simp only [Fri.reducePoints.eq_1, Protocol.PointReduction.eq_1, Except.ok.injEq]
  | cons opening points ih =>
    simp only [Fri.reducePoints.eq_2, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      Bool.and_eq_true, beq_iff_eq, mapError_ok_iff, inverse_refines, Prod.exists,
      reduceCoordinates_refines, ih, Protocol.PointReduction.eq_2, exists_and_left, and_assoc]

theorem reduceMatrix_refines (params : Parameters) (challenges : Fri.Challenges) (index : Nat)
    (matrix : Pcs.Matrix) (row : Array Field) (before after : Fri.ReductionBuckets) :
    Fri.reduceMatrix params challenges index matrix row before = .ok after ↔
      Protocol.MatrixReduction params challenges index matrix row before after := by
  simp only [Fri.reduceMatrix, bind_ok_iff, unit_exists_iff, ensure_ok_iff, pure_ok_iff,
    fri_getAt_refines, queryPoint_refines, Bool.not_eq_true', Array.isEmpty_eq_false_iff,
    reducePoints_refines, Protocol.MatrixReduction, exists_and_left]

theorem reduceMatrices_refines (params : Parameters) (challenges : Fri.Challenges) (index : Nat)
    (matrices : List Pcs.Matrix) (rows : List (Array Field)) (before after : Fri.ReductionBuckets) :
    Fri.reduceMatrices params challenges index matrices rows before = .ok after ↔
      Protocol.MatrixReductions params challenges index matrices rows before after := by
  induction matrices generalizing rows before with
  | nil => cases rows <;> simp [Fri.reduceMatrices, Protocol.MatrixReductions]
  | cons matrix matrices ih =>
    cases rows with
    | nil => simp [Fri.reduceMatrices, Protocol.MatrixReductions]
    | cons row rows =>
      simp only [Fri.reduceMatrices, bind_ok_iff, reduceMatrix_refines, ih, Protocol.MatrixReductions]

theorem reduceBatches_refines (params : Parameters) (challenges : Fri.Challenges) (index query : Nat)
    (openings : Array BatchOpening) (rounds : List Pcs.Round) (batch : Nat) (before after : Fri.ReductionBuckets) :
    Fri.reduceBatches params challenges index query openings rounds batch before = .ok after ↔
      Protocol.BatchReductions params challenges index query openings rounds batch before after := by
  induction rounds generalizing batch before with
  | nil => simp [Fri.reduceBatches, Protocol.BatchReductions]
  | cons round rounds ih =>
    simp only [Fri.reduceBatches, bind_ok_iff, unit_exists_iff, ensure_ok_iff,
      beq_iff_eq, fri_getAt_refines, reduceMatrices_refines, ih, Protocol.BatchReductions, exists_and_left]

theorem checkConstant_refines (buckets : Fri.ReductionBuckets) (height : Nat) :
    Fri.checkConstant buckets height = .ok () ↔ Protocol.ConstantBucket buckets height := by
  simp only [Fri.checkConstant, bind_ok_iff, fri_getAt_refines, Protocol.ConstantBucket]
  apply exists_congr
  intro cell
  cases cell with
  | none => simp [pure_ok_iff]
  | some pair =>
    cases pair
    simp only [ensure_ok_iff, extension_beq_iff_eq]

theorem collectReduced_refines (buckets : Fri.ReductionBuckets) (heights : List Nat) (result : List Fri.ReducedOpening) :
    Fri.collectReduced buckets heights = .ok result ↔ Protocol.ReducedHeights buckets heights result := by
  induction heights generalizing result with
  | nil => simp [Fri.collectReduced, Protocol.ReducedHeights]
  | cons height heights ih =>
    simp only [Fri.collectReduced, bind_ok_iff, pure_ok_iff, fri_getAt_refines, ih,
      Protocol.ReducedHeights, exists_and_left]
    apply exists_congr
    intro cell
    cases cell with
    | none => rfl
    | some pair => cases pair; rfl

theorem reduceQuery_refines (params : Parameters) (challenges : Fri.Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (query : Nat) (result : Array Fri.ReducedOpening) :
    Fri.reduceQuery params challenges rounds openings query = .ok result ↔
      Protocol.ReducedQuery params challenges rounds openings query result := by
  simp only [Fri.reduceQuery, bind_ok_iff, pure_ok_iff, fri_getAt_refines, reduceBatches_refines,
    unit_exists_iff, checkConstant_refines, collectReduced_refines, listArray_exists_iff,
    Protocol.ReducedQuery, exists_and_left]

theorem reduceQueries_refines (params : Parameters) (challenges : Fri.Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (query remaining : Nat) (result : List (Array Fri.ReducedOpening)) :
    Fri.reduceQueries params challenges rounds openings query remaining = .ok result ↔
      Protocol.ReducedQueries params challenges rounds openings query remaining result := by
  induction remaining generalizing query result with
  | zero => simp [Fri.reduceQueries, Protocol.ReducedQueries]
  | succ remaining ih =>
    simp only [Fri.reduceQueries, bind_ok_iff, pure_ok_iff, reduceQuery_refines, ih,
      Protocol.ReducedQueries, exists_and_left]

theorem openInputs_refines (params : Parameters) (challenges : Fri.Challenges) (rounds : Array Pcs.Round)
    (openings : Array BatchOpening) (result : Array (Array Fri.ReducedOpening)) :
    Fri.openInputs params challenges rounds openings = .ok result ↔
      Protocol.InputsOpened params challenges rounds openings result := by
  simp only [Fri.openInputs, bind_ok_iff, unit_exists_iff, pure_ok_iff, authenticateInputs_refines,
    reduceQueries_refines, listArray_exists_iff, Protocol.InputsOpened]

end MultiStark.Verify.Proofs
