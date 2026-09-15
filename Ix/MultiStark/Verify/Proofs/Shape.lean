module
public import Ix.MultiStark.Verify.Protocol.Shape
public import Ix.MultiStark.Verify.Proofs.Key

public section

namespace MultiStark.Verify.Proofs

theorem shape_getAt_refines {α : Type} (values : Array α) (index : Nat) (value : α) :
    Shape.getAt values index = .ok value ↔ values[index]? = some value := by
  unfold Shape.getAt
  cases values[index]? <;> simp

theorem twoRows_refines (width : Nat) (rows : Array (Array Ext)) (result : Array Ext × Array Ext) :
    Shape.twoRows width rows = .ok result ↔ Protocol.TwoRows width rows result := by
  cases result with
  | mk current next =>
    unfold Shape.twoRows Protocol.TwoRows
    generalize rows.toList = values
    cases values with
    | nil => simp
    | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest =>
        cases rest with
        | nil =>
          simp only [bind_ok_iff, unit_exists_iff, ensure_ok_iff, Bool.and_eq_true, beq_iff_eq,
            pure_ok_iff, Prod.mk.injEq, List.cons.injEq, and_true]
          constructor
          · rintro ⟨⟨h1, h2⟩, rfl, rfl⟩
            exact ⟨⟨rfl, rfl⟩, h1, h2⟩
          · rintro ⟨⟨rfl, rfl⟩, h1, h2⟩
            exact ⟨⟨h1, h2⟩, rfl, rfl⟩
        | cons _ _ => simp

theorem oneRow_refines (width : Nat) (rows : Array (Array Ext)) (result : Array Ext) :
    Shape.oneRow width rows = .ok result ↔ Protocol.OneRow width rows result := by
  unfold Shape.oneRow Protocol.OneRow
  generalize rows.toList = values
  cases values with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil =>
      simp only [bind_ok_iff, unit_exists_iff, ensure_ok_iff, beq_iff_eq, pure_ok_iff,
        List.cons.injEq, and_true]
      constructor
      · rintro ⟨width, rfl⟩
        exact ⟨rfl, width⟩
      · rintro ⟨rfl, width⟩
        exact ⟨width, rfl⟩
    | cons _ _ => simp

theorem preprocessedRows_refines (circuit : Circuit) (logDegree : Nat) (prep : OpenedRound)
    (slot : Option Nat) (result : Array Ext × Array Ext) :
    Shape.preprocessedRows circuit logDegree prep slot = .ok result ↔
      Protocol.PreprocessedRows circuit logDegree prep slot result := by
  cases slot <;>
    simp [Shape.preprocessedRows, Protocol.PreprocessedRows, bind_ok_iff, unit_exists_iff,
      ensure_ok_iff, shape_getAt_refines, twoRows_refines]

theorem inactivePreprocessed_refines (prep : OpenedRound) (slot : Option Nat) :
    Shape.inactivePreprocessed prep slot = .ok () ↔ Protocol.InactivePreprocessed prep slot := by
  cases slot <;>
    simp [Shape.inactivePreprocessed, Protocol.InactivePreprocessed, bind_ok_iff, shape_getAt_refines,
      ensure_ok_iff]

theorem activeValues_refines (key : Key) (proof : Proof) (circuit : Circuit) (prepIndex : Option Nat)
    (index pos : Nat) (result : Shape.CircuitValues) :
    Shape.activeValues key proof circuit prepIndex index pos = .ok result ↔
      Protocol.ActiveCircuitValues key proof circuit prepIndex index pos result := by
  simp only [Shape.activeValues, bind_ok_iff, unit_exists_iff, ensure_ok_iff, decide_eq_true_eq,
    shape_getAt_refines, twoRows_refines, oneRow_refines, preprocessedRows_refines, pure_ok_iff,
    Protocol.ActiveCircuitValues, exists_and_left]

theorem checkCircuits_refines (key : Key) (proof : Proof) (circuits : List Circuit)
    (index pos : Nat) (result : List Shape.CircuitValues) :
    Shape.checkCircuits key proof circuits index pos = .ok result ↔
      Protocol.ShapeCircuits key proof circuits index pos result := by
  induction circuits generalizing index pos result with
  | nil => simp [Shape.checkCircuits, Protocol.ShapeCircuits]
  | cons circuit circuits ih =>
    simp only [Shape.checkCircuits, bind_ok_iff, shape_getAt_refines, Protocol.ShapeCircuits]
    apply exists_congr
    intro active
    cases active <;>
      simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_iff, inactivePreprocessed_refines, unit_exists_iff,
        activeValues_refines, ih, pure_ok_iff, exists_and_left]

theorem shape_check_refines (key : Key) (proof : Proof) (result : Array Shape.CircuitValues) :
    Shape.check key proof = .ok result ↔ Protocol.ShapeAccepted key proof result := by
  simp only [Shape.check, bind_ok_iff, unit_exists_iff, mapError_ok_iff, validateKey_refines,
    ensure_ok_iff, Bool.and_eq_true, beq_iff_eq, Array.any_eq_true', id_eq, exists_eq_right,
    checkCircuits_refines, pure_ok_iff, listArray_exists_iff, Protocol.ShapeAccepted, and_assoc]

end MultiStark.Verify.Proofs
