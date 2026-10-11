import Ix.CompileCert.Canon.ExpansionState

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

private theorem extract_mem {α : Type} {values : Array α} {value : α}
    {start stop : Nat} (member : value ∈ values.extract start stop) : value ∈ values := by
  obtain ⟨index,bound,rfl⟩ := Array.mem_extract_iff_getElem.mp member
  exact Array.getElem_mem _

/-- The arguments introduced for the block parameters contain no source reads. -/
theorem RefScope.paramArgs (P : Name → Prop) (np depth : Nat) :
    ∀ argument ∈ Ix.Compile.Canon.paramArgs np depth, RefScope P argument := by
  intro argument member
  obtain ⟨i,_,rfl⟩ := Array.mem_map.mp member
  simp [RefScope]

/-- Replacing a nested occurrence retains its index-reference scope and adds
only the already allocated auxiliary identity. -/
theorem RefScope.nestedReplacement {P : Name → Prop} {e : Expr}
    (scope : RefScope P e) (aux : Name) (known : P aux)
    (levels : Array Ix.Level) (np depth externalParams : Nat) :
    RefScope P
      (Ix.Compile.Canon.mkAppN (Ix.Compile.Canon.mkAppN (Expr.mkConst aux levels) (Ix.Compile.Canon.paramArgs np depth))
        ((Ix.Compile.Canon.getAppFnArgs e).2.extract externalParams (Ix.Compile.Canon.getAppFnArgs e).2.size)) := by
  apply RefScope.mkAppN
  · apply RefScope.mkAppN
    · simpa [RefScope] using known
    · exact RefScope.paramArgs P np depth
  · intro argument member
    exact scope.getAppFnArgs.2 argument (extract_mem member)

/-- The actual auxiliary constructor result rewrite adds only its own
auxiliary head. Its source name comparison may take either branch. -/
theorem RefScope.replaceCtorResultHead {P : Name → Prop} {e : Expr}
    (scope : RefScope P e) (source aux : Name) (known : P aux)
    (externalParams : Nat) (levels : Array Ix.Level) (np depth : Nat) :
    RefScope P (Ix.Compile.Canon.replaceCtorResultHead source aux externalParams levels np e depth) := by
  induction e generalizing depth with
  | forallE name typ body info hash iht ihb =>
    have parts : RefScope P typ ∧ RefScope P body := by
      simpa [RefScope, sourceExprRefs, or_imp, forall_and] using scope
    have tail := ihb parts.2 (depth+1)
    simpa [Ix.Compile.Canon.replaceCtorResultHead, RefScope, sourceExprRefs, or_imp, forall_and] using
      And.intro parts.1 tail
  | mdata data body hash ih =>
    have bodyScope : RefScope P body := scope
    exact ih bodyScope depth
  | _ =>
    simp only [Ix.Compile.Canon.replaceCtorResultHead]
    repeat' first
      | exact scope
      | split
    all_goals
      apply RefScope.mkAppN
      · apply RefScope.mkAppN
        · simpa [RefScope] using known
        · exact RefScope.paramArgs P np depth
      · intro argument member
        apply scope.getAppFnArgs.2 argument
        simpa only [*] using extract_mem member

end Ix.CompileCert.Canon
