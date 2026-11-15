import IxC.Kernel.Units
import Ix.IxVM.Refinement.Claim

/-! # Unit checks under reference theorem storage

Representing a theorem as an opaque definition preserves its names, generated status and unit
boundaries. The units check on the reference declaration array therefore checks the same roots
and ownership as the reader's original declaration array.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

private abbrev refDecl : Declaration .anon → Declaration .anon :=
  IxVM.Refinement.thmToOpaqueDefn

theorem thmToOpaqueDefn_names (d : Declaration .anon) :
    (IxVM.Refinement.thmToOpaqueDefn d).names = d.names := by
  cases d with
  | thmDecl cv value => cases cv.name <;> rfl
  | _ => rfl

private theorem refDecl_isGenerated (d : Declaration .anon) :
    (refDecl d).isGenerated = d.isGenerated := by
  simp only [Declaration.isGenerated, refDecl, thmToOpaqueDefn_names]

private theorem refDecl_isBasis (d : Declaration .anon) :
    (refDecl d).isBasis = d.isBasis := by
  cases d with
  | thmDecl cv value =>
    cases hn : cv.name <;> simp [refDecl, IxVM.Refinement.thmToOpaqueDefn, hn, Declaration.isBasis]
  | _ => rfl

private theorem names_refDecl (ds : List (Declaration .anon)) :
    (ds.map refDecl).flatMap Declaration.names = ds.flatMap Declaration.names := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    change (refDecl d).names ++ (ds.map refDecl).flatMap Declaration.names =
      d.names ++ ds.flatMap Declaration.names
    rw [thmToOpaqueDefn_names, ih]

private theorem unitsGo_refDecl (ds acc : List (Declaration .anon)) :
    unitsGo (acc.map refDecl) (ds.map refDecl) = (unitsGo acc ds).map (List.map refDecl) := by
  induction ds generalizing acc with
  | nil => cases acc <;> simp [unitsGo]
  | cons d ds ih =>
    simp only [List.map_cons, unitsGo, refDecl_isGenerated]
    split
    · exact ih (d :: acc)
    · simp only [List.map_cons, List.map_reverse]
      exact congrArg (List.cons _) (ih [])

private theorem unitSplit_refDecl : ∀ (ds : List (Declaration .anon)),
    unitSplit (ds.map refDecl) =
      (unitSplit ds).map (fun p => (p.1.map refDecl, refDecl p.2))
  | [] => rfl
  | [_] => rfl
  | d :: e :: ds => by
    change (unitSplit ((e :: ds).map refDecl)).map (fun p => (refDecl d :: p.1, p.2)) =
      ((unitSplit (e :: ds)).map (fun p => (d :: p.1, p.2))).map
        (fun p => (p.1.map refDecl, refDecl p.2))
    simp only [unitSplit_refDecl (e :: ds), Option.map_map, Function.comp_def, List.map_cons]

private theorem unitBases_refDecl (ds : List (Declaration .anon)) :
    unitBases (ds.map refDecl) = unitBases ds := by
  simp only [unitBases, names_refDecl]

private theorem genBases_refDecl (ds : List (Declaration .anon)) :
    genBases (ds.map refDecl) = genBases ds := by
  unfold genBases
  rw [unitSplit_refDecl]
  cases unitSplit ds with
  | none => rfl
  | some p => simp [names_refDecl]

private theorem closerBases_refDecl (ds : List (Declaration .anon)) :
    closerBases (ds.map refDecl) = closerBases ds := by
  unfold closerBases
  rw [unitSplit_refDecl]
  cases unitSplit ds with
  | none => rfl
  | some p => simp [refDecl, thmToOpaqueDefn_names]

private theorem unitShapeOk_refDecl (ds : List (Declaration .anon)) :
    unitShapeOk (ds.map refDecl) = unitShapeOk ds := by
  unfold unitShapeOk
  rw [unitSplit_refDecl, genBases_refDecl, closerBases_refDecl]
  cases unitSplit ds with
  | none => rfl
  | some p => simp [refDecl_isGenerated]

private theorem unitShapeMsg_refDecl (ds : List (Declaration .anon)) (i : Nat) :
    unitShapeMsg (ds.map refDecl) i = unitShapeMsg ds i := by
  simp only [unitShapeMsg, genBases_refDecl, closerBases_refDecl]

private theorem checkUnitsGo_refDecl (us : List (List (Declaration .anon)))
    (seen : Std.HashMap (Key .anon) Nat) (i : Nat) :
    checkUnitsGo seen (us.map (List.map refDecl)) i = checkUnitsGo seen us i := by
  induction us generalizing seen i with
  | nil => rfl
  | cons ds us ih =>
    simp [checkUnitsGo, List.any_map, refDecl_isBasis, unitShapeOk_refDecl,
      unitShapeMsg_refDecl, unitBases_refDecl, ih]

/-- The actual cached check's units result transfers from reference theorem storage to the
reader's declaration array. -/
theorem checkUnits_thmToOpaqueDefn (ds : Array (Declaration .anon)) :
    checkUnits (ds.map IxVM.Refinement.thmToOpaqueDefn) = checkUnits ds := by
  change checkUnits (ds.map refDecl) = checkUnits ds
  unfold checkUnits unitsOf
  rw [Array.toList_map]
  have h := unitsGo_refDecl ds.toList []
  simp only [List.map_nil] at h
  rw [h, checkUnitsGo_refDecl]

end IxVM.Refinement.Decl
