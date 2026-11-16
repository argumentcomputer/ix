import IxVMRefinement.Decl.NativeNoRecRun

/-! # Recognition and installation of empty native families

For a reader former whose declared type is a literal sort, the no-recursor recognizer can
recover the zero parameter and index counts directly. The constructed semantic run installs
only that former, preserving its reader annotation and requiring no constructor load facts.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics

private theorem annotates_sort_inv {type : Expr .anon} {level : Level}
    (annotation : IxVM.Consistency.Annotates type (.sort level)) : type = .sort level := by
  cases annotation
  rfl

/-- The no-recursor recognizer accepts an empty family at a literal sort and retains its
actual former. The recursor stub contributes no index count. -/
theorem nativePartsNoRec_empty_sort {cv : ConstantVal .anon} {caps : IndCaps .anon} {level : Level}
    (literal : cv.type = .sort level)
    (notBasis : reservedBasisNames.contains cv.name = false) :
    ∃ parts,
      nativePartsNoRec? 0 [.indInfo cv caps] = some parts ∧
      parts.cvT = cv ∧ parts.nP = 0 ∧ parts.nIdx = 0 ∧ parts.ctors = [] := by
  have stubNotBasis : reservedBasisNames.contains (auxKey cv.name .recursor) = false :=
    reservedBasisNames_contains_auxKey _ _
  cases levelShape : cv.levelParams with
  | nil =>
    simp [nativePartsNoRec?, nativeParts?, nativeShape?, nativeRecStub, sumSplit,
      nativeCounts?, literal, Expr.piBinders, notBasis, stubNotBasis, levelShape, Expr.stripPis]
  | cons head tail =>
    have tailNe : (tail == head :: tail) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro same
      have length := congrArg List.length same
      simp at length
    simp [nativePartsNoRec?, nativeParts?, nativeShape?, nativeRecStub, sumSplit,
      nativeCounts?, literal, Expr.piBinders, notBasis, stubNotBasis, levelShape, tailNe, Expr.stripPis]

/-- A singleton former cannot be any of the complete reserved basis blocks. -/
theorem basisPinHit_single_former (cv : ConstantVal .anon) (caps : IndCaps .anon) :
    basisPinHit [.indInfo cv caps] = none := by
  have noMatch : ∀ kind ∈ [BasisKind.eqK, .natK, .punitK, .emptyK, .falseK],
      (kind.decls.map (·.name) == ([.indInfo cv caps] : List (ConstantInfo .anon)).map (·.name)) = false := by
    intro kind member
    apply beq_eq_false_iff_ne.mpr
    intro same
    have count := congrArg List.length same
    simp only [List.mem_cons, List.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      simp [BasisKind.decls, eqBasis, natBasis, punitBasis, emptyBasis, falseBasis] at count
  unfold basisPinHit
  rw [List.find?_eq_none.mpr noMatch]
  rfl

/-- A literal-sort empty family has a reader-shaped installation and semantic native run.
The checked former supplies every typing obligation; no compatibility load facts are used. -/
theorem native_empty_sort_step {env : Env .anon} {cv annotated : ConstantVal .anon}
    {caps : IndCaps .anon} {level : Level}
    (literal : cv.type = .sort level)
    (stored : IxVM.Consistency.ValStored annotated cv)
    (checked : ConstantValCheckJ Model.rulesJ env cv annotated) :
    IxVM.Consistency.InstallStep env (.indDecl [.indInfo cv caps] 0)
      ⟨.indInfo annotated {} :: env.consts⟩ ∧
    DeclRunJ Model.rulesJ (IndRoutesJ Model.rulesJ env) env (.indDecl [.indInfo cv caps] 0)
      ⟨.indInfo annotated {} :: env.consts⟩ := by
  obtain ⟨parts, recognized, former, params, indices, empty⟩ :=
    nativePartsNoRec_empty_sort (caps := caps) literal checked.inv.2.1
  have annotatedLiteral : annotated.type = .sort level := by
    have annotation := stored.2.2
    rw [literal] at annotation
    exact annotates_sort_inv annotation
  have checked' : ConstantValCheckJ Model.rulesJ env parts.cvT annotated := by
    simpa only [former] using checked
  have run := nativeNoRecRunJ_empty_of_checked (binders := []) (level := level)
    checked' empty (by simp [params, indices, Expr.stripPis, annotatedLiteral])
  have notPinned := basisPinHit_single_former cv caps
  refine ⟨?_, declRunJ_of_nativeNoRec notPinned recognized run⟩
  apply installStep_of_perm_and_optTable (blockA := [.indInfo annotated {}])
    (new_base := [.indInfo annotated {}]) notPinned (by simp)
  · intro ci member
    simp only [List.mem_singleton] at member
    subst ci
    exact checked.fresh
  · exact .cons ⟨stored, trivial⟩ .nil
  · exact .refl _
  · exact .inl rfl

end IxVM.Refinement.Decl
