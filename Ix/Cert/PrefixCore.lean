import Ix.Cert.PrefixReadings
import IxC.Kernel.Model.Fold

/-! # The actual prefix core at the supplied final interpretation

Prefix acceptance supplies only the model-free WF/projection/constructor
Props. Every interpreted field is copied from the supplied FINAL model or
transported by its actual preserved lookups. The core's acval is literally
the final acval. This is not a prefix StrongModel or complete RulesInputs.
-/

namespace Ix.Cert.PrefixCore

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Cert.ReferenceFronts

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- Eliminate prefix model existence ONLY into this model-free Prop triple.
No witness valuation or semantic field leaves the elimination. -/
theorem prefix_syntax
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] :
    EnvWF before ∧ ProjOkT before ∧ RecCtorsStored before := by
  obtain ⟨_, _, prefixRun, _, _, _, _, _⟩ := front
  have accepted : checkDeclsPure .verified (fueledOps .verified F) ev (ds.take i) = .ok before := prefixRun
  exact (checkDeclsPure_sound_of (V := V) rfl accepted).elim fun witness =>
    ⟨witness.base2.wf, witness.base2.proj_ok, witness.base2.rec_ctors⟩

/-- Internal carrier constructor. The actual-front wrapper below derives
both Prop inputs. Basis pins and parameter dependence use FINAL leaves. -/
def coreAt {V : Type w} [SetTheory V] (M : Cached.StrongModel V envA)
    (facts : EnvWF before ∧ ProjOkT before ∧ RecCtorsStored before)
    (lookup : FindPreserved before envA) : EnvModel V before where
  wf := facts.1
  acval := M.internal.base2.acval
  cval_closedL := M.internal.base2.cval_closedL
  basis_pinnedL := fun n ci found reserved =>
    M.internal.base2.basis_pinnedL n ci (lookup found) reserved
  proj_ok := facts.2.1
  rec_ctors := facts.2.2
  acval_closed := M.internal.base2.acval_closed
  acval_params := fun n ci found φ ψ agree =>
    M.internal.base2.acval_params n ci (lookup found) φ ψ agree
  acval_wellDenoted := M.internal.base2.acval_wellDenoted

theorem coreAt_acval {V : Type w} [SetTheory V] (M : Cached.StrongModel V envA)
    (facts : EnvWF before ∧ ProjOkT before ∧ RecCtorsStored before)
    (lookup : FindPreserved before envA) :
    (coreAt M facts lookup).acval = M.internal.base2.acval := rfl

theorem coreAt_cval {V : Type w} [SetTheory V] (M : Cached.StrongModel V envA)
    (facts : EnvWF before ∧ ProjOkT before ∧ RecCtorsStored before)
    (lookup : FindPreserved before envA) :
    cvalOf (coreAt M facts lookup).acval = M.model.cval := rfl

/-- The real indexed prefix and current/suffix run derive all the core's
inputs. Both interpretations are fixed definitionally at EVERY key/level. -/
theorem core_of_front
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧ cvalOf core.acval = M.model.cval := by
  exact ⟨coreAt M (prefix_syntax front V) front.lookup_preserved, rfl, rfl⟩

end Ix.Cert.PrefixCore

namespace Ix.Cert.ReferenceFronts

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model Ix.Kernel.SetTheory
open Ix.Kernel.Model.Rules (Graded)
open Ix.Cert.PrefixCore

universe w
variable {md : Mode} {ev : Evidences md} {ds : List (Declaration md)}
  {envA before : Env md} {i F : Nat} {cv : Ix.Kernel.ConstantVal md}
  {raw expected checked : Ix.Kernel.Expr md} {hint : ReducibilityHint}

/-- The actual indexed front produces its prefix carrier at the supplied
FINAL interpretation, its directly transferable basic laws, and the target
semantic package. All other RulesInputs rows, baseline grading/equality,
full prefix StrongModel and source-form/provenance obligations remain open.
No acceptance witness's interpretation or semantic law is substituted. -/
theorem DefinitionFrontAt.final_prefix_core
    (front : DefinitionFrontAt ev ds envA i cv raw hint F before expected checked)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ core : EnvModel V before,
      core.acval = M.internal.base2.acval ∧
      cvalOf core.acval = M.model.cval ∧
      AcvalValid core ∧
      (∀ φ : LevelParam → Nat, NatHeads core φ) ∧
      EqLaw core ∧
      ∀ φ : LevelParam → Nat,
        ∃ ha,
          denoteMeta core.acval before φ 0 expected = some ha ∧
          Graded V [] ha ∧
          denoteMeta core.acval before φ 0 checked = some (core.acval cv.name φ) ∧
          Graded V [] (core.acval cv.name φ) ∧
          ∀ ρ : BVarIdx → V, interp V ρ (core.acval cv.name φ) ∈ˢ interp V ρ ha := by
  obtain ⟨core, acvalEq, cvalEq⟩ := core_of_front front V M
  have lookup : FindPreserved before envA := front.lookup_preserved
  refine ⟨core, acvalEq, cvalEq, ?_, ?_, ?_, ?_⟩
  · simpa only [AcvalValid, acvalEq] using M.internal.acval_validV
  · intro φ support
    simpa only [acvalEq] using M.internal.nat_heads φ (PrefixReadings.nat_support lookup support)
  · intro found
    simpa only [acvalEq] using M.internal.eq_law (lookup found)
  · intro φ
    obtain ⟨ha, headerRead, _, headerGrade, valueRead, valueGrade, member⟩ :=
      front.final_semantic_front V M φ
    refine ⟨ha, ?_, headerGrade, ?_, ?_, ?_⟩
    · simpa only [acvalEq] using headerRead
    · simpa only [acvalEq] using valueRead
    · simpa only [acvalEq] using valueGrade
    · simpa only [acvalEq] using member

end Ix.Cert.ReferenceFronts
