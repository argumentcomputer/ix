module

public import IxC.Kernel.Model.Inductives.StructStageTable
public section

/-!
# The direct structure's install, assembled (task #175 W4c, P3 module 7, part 9; S1)

`declStructP`: the P carrier survives the direct install's run
(`DeclStructRun`).  The stages compose as the checker runs them —
former, constructor, recursor, the projection table (task #175 S1:
one cons, `stageTable`) — with one twist: the
former's leaf mentions the field chain, which is read off the
constructor's stored type, checked *after* the former is stored.  So
the former is installed twice: once with an empty field chain, only
to read the constructor's data at a carrier that stores the former
(`ctorData_of` needs the former's lookup), then with the real chain.
The field readings agree across the two installs because the field
domains resolve in the pre-block environment
(`denoteP_openPis_agree` over `denoteMeta_acvalWith_unmentioned₂`) — the
constructor stage's `constsResolve env₀` re-check is exactly this
fact.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory Ix.Kernel.SetTheory.Tower
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts
  BinderMeta ProjEntry projFnName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Readings under two leaves -/

/-- A name fresh at a cons is fresh below it. -/
theorem find?_none_of_cons {c : ConstantInfo} {env : Env} {n : Name}
    (h : Env.find? ⟨c :: env.consts⟩ n = none) : env.find? n = none := by
  rw [Ix.Kernel.Env.find?_cons] at h
  split at h
  · exact nomatch h
  · exact h

/-! ## The assembly -/

end Ix.Kernel.Model
