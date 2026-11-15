import IxVMRefinement.Decl.ReferenceStorage
import IxVMRefinement.Decl.RoleUnits
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
  cases pinned : basisPinHit block with
  | none => simp only [IxVM.Consistency.installs, pinned, Declaration.names]
  | some kind =>
    have rawNames : block.map (·.name) = kind.decls.map (·.name) := by
      unfold basisPinHit at pinned
      have selected := (Option.filter_eq_some_iff.mp pinned).1
      have namesMatch := List.find?_some selected
      exact (eq_of_beq namesMatch).symm
    have annotatedNames : (kind.declsA (md := .anon)).map (·.name) =
        (kind.decls (md := .anon)).map (·.name) := by
      cases kind <;> decide
    simpa only [IxVM.Consistency.installs, pinned, Declaration.names] using
      annotatedNames.trans rawNames.symm

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
  simp only [unitShapeOk, Bool.and_eq_true] at shape
  have bases : (genBases unit).all (closerBases unit).contains = true := shape.2
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
    simpa only [checkUnits, List.toList_toArray] using units
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


/-- The reader's generated roots are present in the accepted reference theorem-storage view. -/
theorem ReferenceTrace.raw_unit_roots {fuel : Nat} {env out : Env .anon}
    {ds unit generated : List (Declaration .anon)} {block : List (ConstantInfo .anon)} {nP : Nat}
    (trace : ReferenceTrace fuel env (ds.map IxVM.Refinement.thmToOpaqueDefn) out)
    (units : checkUnits ds.toArray = .ok ())
    (inUnits : unit ∈ unitsOf ds)
    (split : unitSplit unit = some (generated, .indDecl block nP))
    (underived : DeclNonAux (.indDecl block nP)) :
    ∀ d ∈ generated, ∀ name ∈ d.names, (out.find? name.base).isSome = true := by
  have mappedUnits : checkUnits (ds.map IxVM.Refinement.thmToOpaqueDefn).toArray = .ok () := by
    rw [← List.map_toArray, checkUnits_thmToOpaqueDefn]
    exact units
  have mappedMember : unit.map IxVM.Refinement.thmToOpaqueDefn ∈
      unitsOf (ds.map IxVM.Refinement.thmToOpaqueDefn) := by
    rw [unitsOf_thmToOpaqueDefn]
    exact List.mem_map_of_mem inUnits
  have mappedSplit : unitSplit (unit.map IxVM.Refinement.thmToOpaqueDefn) =
      some (generated.map IxVM.Refinement.thmToOpaqueDefn, .indDecl block nP) := by
    rw [unitSplit_thmToOpaqueDefn, split]
    rfl
  have roots := trace.unit_roots mappedUnits mappedMember mappedSplit underived
  intro d hd name hn
  exact roots (IxVM.Refinement.thmToOpaqueDefn d) (List.mem_map_of_mem hd) name
    (by rw [thmToOpaqueDefn_names]; exact hn)

end IxVM.Refinement.Decl
