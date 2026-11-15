import IxVMRefinement.Decl.ReferenceStorage
import IxVMRefinement.Decl.RoleUnits
import Ix.Cert.SourceInstalls
import IxC.Kernel.Verify.Rename.UnionUnits

/-! # Declared auxiliary roots at accepted unit endpoints

The executable units check ties every generated declaration's base to the closing inductive
declaration. The actual reference trace supplies that closer's installed names, including
normalized native entries and pinned basis blocks.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- An inductive declaration and its public installation name the same constants, including pins. -/
theorem indDecl_installs_names (block : List (ConstantInfo .anon)) (nP : Nat) :
    (IxVM.Consistency.installs (.indDecl block nP)).map (·.name) =
      (Declaration.indDecl block nP).names := by
  unfold IxVM.Consistency.installs
  cases pinned : basisPinHit block with
  | none => rfl
  | some kind =>
    exact (Ix.Cert.SourceInstalls.declsA_names kind).trans
      (Ix.Cert.SourceInstalls.basisPinHit_names pinned).symm

private theorem unitSplit_append {md : Mode} :
    ∀ {unit generated : List (Declaration md)} {closer : Declaration md},
      unitSplit unit = some (generated, closer) → unit = generated ++ [closer]
  | [], _, _, h => by cases h
  | [d], _, _, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rfl
  | d :: e :: ds, generated, closer, h => by
    change (unitSplit (e :: ds)).map (fun pair => (d :: pair.1, pair.2)) = some (generated, closer) at h
    obtain ⟨⟨gs, last⟩, split, same⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    rw [unitSplit_append split]
    rfl

/-- The actual shape check places every generated name's base among the closer's bases. -/
theorem unitShape_generated_bases {md : Mode} {unit generated : List (Declaration md)}
    {closer : Declaration md} (split : unitSplit unit = some (generated, closer))
    (shape : unitShapeOk unit = true) {d : Declaration md} (declared : d ∈ generated)
    {name : Key md} (named : name ∈ d.names) : name.base ∈ closer.names.map Key.base := by
  have bases : (genBases unit).all (closerBases unit).contains = true :=
    (Bool.and_eq_true.mp shape).2
  have inGenerated : name.base ∈ genBases unit := by
    simp only [genBases, split]
    exact List.mem_map.mpr ⟨name, List.mem_flatMap.mpr ⟨d, declared, named⟩, rfl⟩
  have covered := List.all_eq_true.mp bases name.base inGenerated
  simpa only [closerBases, split, List.contains_iff_mem] using covered

/-- A generated declaration's owner root is actually present after its checked unit. -/
theorem ReferenceTrace.unit_roots {fuel : Nat} {env out : Env .anon}
    {ds unit generated : List (Declaration .anon)} {block : List (ConstantInfo .anon)} {nP : Nat}
    (trace : ReferenceTrace fuel env ds out)
    (units : checkUnits ds.toArray = .ok ())
    (inUnits : unit ∈ unitsOf ds)
    (split : unitSplit unit = some (generated, .indDecl block nP))
    (underived : DeclNonAux (.indDecl block nP)) :
    ∀ d ∈ generated, ∀ name ∈ d.names, (out.find? name.base).isSome = true := by
  have unitsRun : checkUnitsGo {} (unitsOf ds) 0 = .ok () := by
    simpa only [checkUnits, List.toArray_toList] using units
  have shape := ((checkUnitsGo_ok_iff {} (unitsOf ds) 0).mp unitsRun).2.1 unit inUnits
  have closerMember : Declaration.indDecl block nP ∈ ds := by
    rw [← unitsOf_flatten ds]
    apply List.mem_flatten.mpr
    refine ⟨unit, inUnits, ?_⟩
    rw [unitSplit_append split]
    exact List.mem_append_right _ List.mem_cons_self
  intro d declared name named
  have covered := unitShape_generated_bases split shape declared named
  obtain ⟨owner, ownerMember, sameBase⟩ := List.mem_map.mp covered
  rw [← indDecl_installs_names] at ownerMember
  obtain ⟨ci₀, installed, sameName⟩ := List.mem_map.mp ownerMember
  have baseName : ci₀.name.base = ci₀.name :=
    base_of_isBaseKey (isBaseKey_of_nonAuxKey (underived.1 ci₀ installed).1)
  have rootName : name.base = ci₀.name := by
    rw [← sameBase, ← sameName, baseName]
  rw [rootName]
  exact trace.declared closerMember installed

end IxVM.Refinement.Decl
