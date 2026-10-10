import Ix.CompileCert.Pj.RecRead
import Ix.CompileCert.Pj.TeleTyped

/-! Syntax laws linking the checked reader telescopes to typed argument tuples. -/

namespace Ix.CompileCert.Pj

theorem zipMetas_length (ts : List Kernel.Expr) (ms : List Kernel.BinderMeta)
    (length : ms.length = ts.length) : (zipMetas ts ms).length = ts.length := by
  induction ts generalizing ms with
  | nil => rfl
  | cons t ts ih =>
    cases ms with
    | nil => simp at length
    | cons m ms =>
      simp only [zipMetas, List.length_cons]
      rw [ih ms (by simpa using length)]

theorem zipMetas_types (ts : List Kernel.Expr) (ms : List Kernel.BinderMeta)
    (length : ms.length = ts.length) : (zipMetas ts ms).map Prod.fst = ts := by
  induction ts generalizing ms with
  | nil => rfl
  | cons t ts ih =>
    cases ms with
    | nil => simp at length
    | cons m ms =>
      simp only [zipMetas, List.map_cons]
      rw [ih ms (by simpa using length)]

theorem liftTypes_eq_mapIdx (amount cutoff : Nat) (ts : List Kernel.Expr) :
    liftTypes amount cutoff ts =
      ts.mapIdx (fun i t => t.liftLooseBVars amount (cutoff + i)) := by
  induction ts generalizing cutoff with
  | nil => rfl
  | cons t ts ih =>
    simp only [liftTypes, List.mapIdx_cons, Nat.add_zero, ih,
      Nat.add_assoc, Nat.add_comm 1]

theorem liftTypes_length (amount cutoff : Nat) (ts : List Kernel.Expr) :
    (liftTypes amount cutoff ts).length = ts.length := by
  rw [liftTypes_eq_mapIdx]
  exact List.length_mapIdx

theorem liftTele_types (amount cutoff : Nat)
    (bs : List (Kernel.Expr × Kernel.BinderMeta)) :
    (liftTele amount cutoff bs).map Prod.fst =
      liftTypes amount cutoff (bs.map Prod.fst) := by
  rw [liftTypes_eq_mapIdx]
  ext1 i
  simp [liftTele, Option.map_map, Function.comp_def]

theorem liftTele_length (amount cutoff : Nat)
    (bs : List (Kernel.Expr × Kernel.BinderMeta)) :
    (liftTele amount cutoff bs).length = bs.length := by
  simp only [liftTele, List.length_mapIdx]

theorem motive_tele_length (np : Nat) (m : MotiveRd) :
    (m.tele np).length = m.idxs.length + 1 := by
  simp [MotiveRd.tele]

theorem motiveBinders_length (R : RecRd) : R.motiveBinders.length = R.nm := by
  simp only [RecRd.motiveBinders, List.length_mapIdx, RecRd.nm]

theorem minorBinders_length (R : RecRd) : R.minorBinders.length = R.nmin := by
  simp only [RecRd.minorBinders, List.length_mapIdx, RecRd.nmin]

theorem fieldTys_length (np : Nat) (motives : List MotiveRd) (n : MinorRd) :
    (n.fieldTys np motives).length = n.fields.length := by
  simp only [MinorRd.fieldTys, List.length_mapIdx]

theorem ihTys_length (nm : Nat) (n : MinorRd) :
    (n.ihTys nm).length = n.recFields.length := by
  simp only [MinorRd.ihTys, List.length_mapIdx]

theorem finalBinders_types {env : Kernel.Env} {r : Kernel.Name} {R : RecRd}
    (checked : R.Check env r) :
    R.finalBinders.map Prod.fst =
      liftTypes (R.nm + R.nmin) 0 ((R.majorMotive.tele R.np).map Prod.fst) := by
  have length : R.finalMetas.length =
      ((liftTele (R.nm + R.nmin) 0 (R.majorMotive.tele R.np)).map Prod.fst).length := by
    simpa only [List.length_map, liftTele_length] using checked.2.2.1
  rw [RecRd.finalBinders, zipMetas_types _ _ length, liftTele_types]

end Ix.CompileCert.Pj
