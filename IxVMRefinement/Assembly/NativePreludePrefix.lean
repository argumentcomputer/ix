import IxVMRefinement.Assembly.NativePreludeCoverage
import IxVMRefinement.Assembly.NativeRolePrefix
import IxVMRefinement.Decl.RoleUnits

/-! # Prelude former names in the actual accepted prefix

Preparation can choose an input declaration in place of a prelude declaration. It preserves
that declaration's first name. The actual accepted reference check then supplies name
presence, including the quotient package's deferred installation cases.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

/-- Preparation preserves a prelude declaration's first name, including when an input
record replaces the prelude record. -/
theorem prepared_prelude_head {md : Mode} (prelude : Frontend.PreludeIx md)
    (input : Array (Declaration md)) {declaration : Declaration md} {key : Key md}
    (declared : declaration ∈ prelude.decls.toList)
    (head : Frontend.preludeKey declaration = some key) :
    ∃ actual ∈ (Frontend.preparePrelude prelude input).toList, key ∈ actual.names := by
  obtain ⟨actual, member, sameOrDeclared⟩ :=
    Ix.Cert.SourceInstalls.frontSpec_cover prelude.decls.toList input.toList declaration declared
  refine ⟨actual, ?_, ?_⟩
  · rw [Frontend.preparePrelude_front, Array.toList_append, (Frontend.frontOf_toList _ _ _).1]
    exact List.mem_append_left _ (List.mem_append_right _ member)
  · rcases sameOrDeclared with rfl | selected
    · exact List.mem_of_head? head
    · simpa only [Frontend.declares, head, Option.any_some, List.contains_iff_mem] using selected

/-- Every successfully prepared table prelude contributes the quotient type name to
its actual prepared stream. -/
theorem prepared_quot_of_preludeFor {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude) (input : Array (Declaration .anon)) :
    ∃ declaration ∈ (Frontend.preparePrelude prelude.ix input).toList,
      quotName ∈ declaration.names := by
  have named : [Key.role (md := .anon) .quot] ∈ prelude.ix.decls.toList.map (·.names) := by
    rw [preludeFor_shape prepared]
    exact List.mem_map.mpr ⟨[.quot], by decide, rfl⟩
  obtain ⟨declaration, declared, names⟩ := List.mem_map.mp named
  apply prepared_prelude_head prelude.ix input declared
  simpa only [Frontend.preludeKey, names, List.head?_cons]

/-- The actual admission check retains each declared non-sorry name in its reference
store. Quotient side records are covered by the quotient type in this same preparation. -/
theorem admitted_prepared_name_present {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {declaration : Declaration .anon} {key : Key .anon}
    (declared : declaration ∈ (Frontend.preparePrelude witness.prelude.ix witness.fullDecls).toList)
    (named : key ∈ declaration.names) (notSorry : key ≠ sorryAxName) :
    (witness.checkedEnv.find? key).isSome = true := by
  obtain ⟨quotient, quotientDeclared, quotientNamed⟩ :=
    prepared_quot_of_preludeFor witness.preludeRead witness.fullDecls
  have quotientPresent : ∃ d ∈
      (Frontend.preparePrelude witness.prelude.ix witness.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn,
      quotName ∈ d.names :=
    ⟨IxVM.Refinement.thmToOpaqueDefn quotient,
      List.mem_map.mpr ⟨quotient, quotientDeclared, rfl⟩, by
        rwa [Decl.thmToOpaqueDefn_names]⟩
  have actualDeclared : IxVM.Refinement.thmToOpaqueDefn declaration ∈
      (Frontend.preparePrelude witness.prelude.ix witness.fullDecls).toList.map IxVM.Refinement.thmToOpaqueDefn :=
    List.mem_map.mpr ⟨declaration, declared, rfl⟩
  have actualNamed : key ∈ (IxVM.Refinement.thmToOpaqueDefn declaration).names := by
    rwa [Decl.thmToOpaqueDefn_names]
  obtain ⟨constant, stored, same⟩ := Ix.Cert.SourceInstalls.accepts_names
    witness.accepted quotientPresent actualDeclared actualNamed notSorry
  rw [← same]
  exact Decl.env_find?_isSome_of_mem stored

/-- A prelude declaration's actual head has a stored name in the accepted prefix. -/
theorem admitted_prelude_head_present {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {declaration : Declaration .anon} {key : Key .anon}
    (declared : declaration ∈ witness.prelude.ix.decls.toList)
    (head : Frontend.preludeKey declaration = some key) :
    (witness.checkedEnv.find? key).isSome = true := by
  obtain ⟨role, roleMember, keyEq⟩ :=
    (preludeFor_decls_roles witness.preludeRead).2 declaration declared key (List.mem_of_head? head)
  have notSorry : key ≠ sorryAxName := by
    rw [keyEq]
    have allowed : ∀ r ∈ preludeShape.flatten, r ≠ Role.sorryAx := by decide
    intro same
    exact allowed role roleMember (Key.role.inj same)
  obtain ⟨actual, actualDeclared, named⟩ :=
    prepared_prelude_head witness.prelude.ix witness.fullDecls declared head
  exact admitted_prepared_name_present witness actualDeclared named notSorry

/-- The actual native former read from a prelude parent is already present in the
accepted reference prefix under its concrete prelude-reader name. -/
theorem admitted_prelude_native_former_present {V : IxVM.Refinement.View} {binding : Admission.Binding}
    (witness : IxVM.Consistency.ReaderAdmissionWitness V binding)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (present : (owner, source) ∈ witness.prelude.records) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)]) :
    ∃ key, (nativePreludeReaderCtx witness.table witness.prelude).memberKey (.member owner member) = .ok key ∧
      (witness.checkedEnv.find? key).isSome = true := by
  obtain ⟨key, read, declaration, declared, head⟩ :=
    prelude_native_former_head witness.preludeRead present kind memberAt one
  exact ⟨key, read, admitted_prelude_head_present witness declared head⟩

end IxVM.Refinement.Assembly
