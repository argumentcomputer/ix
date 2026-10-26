import Ix.Compile.SourceInput.GroupPlan
import Ix.CompileCert.Loop
import IxC.Kernel.Audit.Axioms

namespace Ix.Cert.SourceGroupPlan
open Ix.LeanIngress Ix.Compile.SourceInput Ix.Compile.SourceInput.GroupPlan

theorem inductive_default (env : Ix.Environment) (first : Ix.InductiveVal) (candidates : Array Ix.RecursorVal) :
    inductiveGroup env first candidates =
      Id.run (inductiveGroupUsing (m := Id) (env.consts.get? ·) first candidates) := rfl
theorem component_default (env : Ix.Environment) (members : Ix.Set Ix.Name) :
    componentGroup env members = Id.run (componentGroupUsing (m := Id) (env.consts.get? ·) members) := rfl

theorem inductive_congr {m : Type → Type} [Monad m] {left right : Ix.Name → m (Option Ix.ConstantInfo)}
    (same : ∀ n, left n = right n) (first : Ix.InductiveVal) (candidates : Array Ix.RecursorVal) :
    inductiveGroupUsing left first candidates = inductiveGroupUsing right first candidates := by
  rw [funext same]
theorem component_congr {m : Type → Type} [Monad m] {left right : Ix.Name → m (Option Ix.ConstantInfo)}
    (same : ∀ n, left n = right n) (members : Ix.Set Ix.Name) :
    componentGroupUsing left members = componentGroupUsing right members := by rw [funext same]

/-- Some is exactly a successful original canonical lookup. Errors are
never converted into a successful value or a placeholder declaration. -/
theorem lookup_some_iff (carrier : Carrier) (name : Ix.Name) (ci : Ix.ConstantInfo) :
    lookup carrier name = .ok (some ci) ↔ carrier.canonicalAt name = .ok ci := by
  cases ran : carrier.canonicalAt name with
  | ok value => simp [lookup,ran]
  | error e => cases e <;> simp [lookup,ran]

/-- None is genuine raw-domain absence, not header or canon failure. -/
theorem lookup_none_iff (carrier : Carrier) (name : Ix.Name) :
    lookup carrier name = .ok none ↔ carrier.byName.get? name = none := by
  cases found : carrier.byName.get? name with
  | none =>
    rw [Std.HashMap.get?_eq_getElem?] at found
    simp [lookup,Carrier.canonicalAt,found,throw,throwThe,MonadExceptOf.throw]
  | some raw =>
    rw [Std.HashMap.get?_eq_getElem?] at found
    by_cases named : (raw.1 == raw.2.name) = true
    · cases canonical : canonical? raw <;>
        simp [lookup,Carrier.canonicalAt,found,named,canonical,pure,Except.pure]
    · simp [lookup,Carrier.canonicalAt,found,named,bind,Except.bind]

theorem header_error {carrier : Carrier} {name : Ix.Name} {requested tuple header}
    (ran : carrier.canonicalAt name = .error (.headerMismatch requested tuple header)) :
    lookup carrier name = .error (.source (.headerMismatch requested tuple header)) := by
  simp only [lookup,ran]
theorem canonical_error {carrier : Carrier} {name requested : Ix.Name}
    (ran : carrier.canonicalAt name = .error (.canonicalMissing requested)) :
    lookup carrier name = .error (.source (.canonicalMissing requested)) := by simp only [lookup,ran]

/-- Success retains the literal canonical result of the same raw winner.
The existing SourceInput provenance theorem can identify it with constS. -/
theorem lookup_origin {carrier : Carrier} {name : Ix.Name} {ci : Ix.ConstantInfo}
    (accepted : lookup carrier name = .ok (some ci)) :
    ∃ raw, carrier.byName.get? name = some raw ∧ raw.1 = raw.2.name ∧ canonical? raw = some ci := by
  have ran := (lookup_some_iff carrier name ci).mp accepted
  cases found : carrier.byName.get? name with
  | none =>
    rw [Std.HashMap.get?_eq_getElem?] at found
    simp [Carrier.canonicalAt,found] at ran
  | some raw =>
    rw [Std.HashMap.get?_eq_getElem?] at found
    by_cases named : (raw.1 == raw.2.name) = true
    · cases canonical : canonical? raw with
      | none => simp [Carrier.canonicalAt,found,named,canonical] at ran
      | some value =>
        have same : value = ci := by
          simpa [Carrier.canonicalAt,found,named,canonical,pure,Except.pure] using ran
        exact ⟨raw,rfl,beq_iff_eq.mp named,same ▸ canonical⟩
    · simp [Carrier.canonicalAt,found,named,bind,Except.bind] at ran

theorem absent_recipe {carrier : Carrier} {name : Ix.Name} (absent : carrier.byName.get? name = none) :
    require carrier name = .error (.absentRecipe name) := by
  rw [require,(lookup_none_iff carrier name).mpr absent]
  rfl

theorem family_head_source_error {carrier : Carrier} {head : Ix.Name} {candidates : Array Ix.Name}
    {e : GroupPlan.Error}
    (failed : lookup carrier head = .error e) :
    materialize carrier (.family head candidates) = .error e := by
  simp [materialize,require,failed,bind,Except.bind]

theorem family_wrong_head {carrier : Carrier} {head : Ix.Name} {candidates : Array Ix.Name}
    {ci : Ix.ConstantInfo} (found : lookup carrier head = .ok (some ci))
    (wrong : ∀ value, ci ≠ .inductInfo value) :
    materialize carrier (.family head candidates) = .error (.expectedInductive head) := by
  cases ci <;> simp_all [materialize,require,bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw]

theorem recursor_source_error {carrier : Carrier} {name : Ix.Name} {e : GroupPlan.Error}
    (failed : lookup carrier name = .error e) : recursor carrier name = .error e := by
  simp [recursor,require,failed,bind,Except.bind]

theorem family_candidates_error {carrier : Carrier} {head : Ix.Name} {candidates : Array Ix.Name}
    {first : Ix.InductiveVal} {e : GroupPlan.Error}
    (found : lookup carrier head = .ok (some (.inductInfo first)))
    (failed : candidates.mapM (recursor carrier) = .error e) :
    materialize carrier (.family head candidates) = .error e := by
  simp [materialize,require,found,failed,bind,Except.bind,pure,Except.pure]

theorem component_run (carrier : Carrier) (key : Ix.Name) (members : Ix.Set Ix.Name) :
    materialize carrier (.component key members) = componentGroupUsing (lookup carrier) members := rfl

theorem unplaced_run {carrier : Carrier} {key : Ix.Name} {ci : Ix.ConstantInfo}
    (found : lookup carrier key = .ok (some ci)) :
    materialize carrier (.unplaced key) = .ok (some (unplaced key ci)) := by
  simp [materialize,require,found,bind,Except.bind,pure,Except.pure]

theorem summary_names (group : Group) : (summarize group).names = group.names := rfl
theorem summary_invalid (names : Array Ix.Name) (error : Ix.Kernel.Reader.ReadError) :
    summarize (.invalid names error) = ⟨names,.invalid error⟩ := rfl

#guard_kernel_axioms inductive_default [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms component_default [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms inductive_congr [propext, Quot.sound]
#guard_kernel_axioms component_congr [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms lookup_none_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms lookup_some_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms lookup_origin [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms header_error [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms canonical_error [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms family_head_source_error [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms family_wrong_head [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms recursor_source_error [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms family_candidates_error [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms unplaced_run [propext, Classical.choice, Quot.sound]

end Ix.Cert.SourceGroupPlan
