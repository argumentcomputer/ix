import Ix.Kernel.Verify.DefinitionDependencies
import Ix.Kernel.Verify.DefinitionReferences
import Ix.Kernel.Verify.Consistency.Production

/-!
Production definition admission supplies a concrete dependency order.
The same reference collector also bounds every reference in the model reading
of the checked type and value. These facts connect the new admission guard to
the preceding model interface; no semantic typing is assumed by this bridge.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

private def AllReferences (available : ConstRef β → Prop) : VExpr β → Prop
  | .bvar _ | .sort _ | .natLit _ => True
  | .const ref _ => available ref
  | .app fn arg | .lam fn arg | .forallE fn arg =>
      AllReferences available fn ∧ AllReferences available arg
  | .proj ref _ major => available ref ∧ AllReferences available major

private theorem allReferences_erase (available : ConstRef β → Prop) (source : AExpr β) :
    AllReferences available source.erase ↔ ∀ ref ∈ source.references, available ref := by
  induction source <;> simp_all [AllReferences, AExpr.erase, AExpr.references, or_imp, forall_and]

private theorem allReferences_liftN {available : ConstRef β → Prop}
    {source : VExpr β} (references : AllReferences available source) (count cutoff : Nat) :
    AllReferences available (source.liftN count cutoff) := by
  induction source generalizing cutoff <;> simp_all [VExpr.liftN, AllReferences]

private theorem allReferences_inst {available : ConstRef β → Prop}
    {body value : VExpr β} (bodyReferences : AllReferences available body)
    (valueReferences : AllReferences available value) (cutoff : Nat) :
    AllReferences available (body.inst value cutoff) := by
  induction body generalizing cutoff with
  | bvar index =>
      simp only [VExpr.inst, VExpr.instVar]
      split
      · trivial
      · split
        · exact allReferences_liftN valueReferences cutoff 0
        · trivial
  | _ => simp_all [VExpr.inst, AllReferences]

private theorem option_bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

private theorem readScopedExpr?_allReferences {available : ConstRef β → Prop}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {term : KExpr .anon} {source : VExpr β} {depth : Nat}
    (reading : readScopedExpr? resolve locals term depth = some source)
    (references : ∀ id, DefinitionReferences.Reference id term →
      ∀ ref, resolve id.addr = some ref → available ref) : AllReferences available source := by
  induction term generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at reading
      split at reading
      · cases reading; trivial
      · contradiction
  | fvar id name info =>
      obtain ⟨index, _, equality⟩ := Option.map_eq_some_iff.mp reading
      cases equality
      trivial
  | sort _ _ | nat _ _ _ => cases reading; trivial
  | str _ _ _ => contradiction
  | letE name domain value body nonDep info _ ihValue ihBody =>
      obtain ⟨A, v, b, _, valueReads, bodyReads, rfl⟩ := readScopedExpr?_let_parts reading
      exact allReferences_inst
        (ihBody bodyReads (fun id reference => references id
          (.child (by simp [DefinitionReferences.Children]) reference)))
        (ihValue valueReads (fun id reference => references id
          (.child (by simp [DefinitionReferences.Children]) reference))) 0
  | const id levels info =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      cases reading
      exact references id (.head (by simp [DefinitionReferences.Heads])) ref resolved
  | app fn arg info ihFn ihArg | lam _ _ fn arg info ihFn ihArg | all _ _ fn arg info ihFn ihArg =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := option_bind_success reading
      obtain ⟨a, aReads, reading⟩ := option_bind_success reading
      cases reading
      exact ⟨ihFn fReads (fun id reference => references id
          (.child (by simp [DefinitionReferences.Children]) reference)),
        ihArg aReads (fun id reference => references id
          (.child (by simp [DefinitionReferences.Children]) reference))⟩
  | prj id field major info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := option_bind_success reading
      obtain ⟨value, valueReads, reading⟩ := option_bind_success reading
      cases reading
      exact ⟨references id (.head (by simp [DefinitionReferences.Heads])) ref resolved,
        ih valueReads (fun id reference => references id
          (.child (by simp [DefinitionReferences.Children]) reference))⟩

/-- Every reference in a model reading is backed by an actual collected
kernel dependency. This also covers opened locals; they add no constants. -/
theorem readScopedExpr?_referencesIn {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {roots : List (KExpr .anon)} {support : RunSupport}
    (coverage : ∀ root ∈ roots, root.ValidationCoverage support)
    (collision : support.CollisionFree) {term : KExpr .anon} (member : term ∈ roots)
    {source : AExpr β} {locals : List FVarId} {depth : Nat}
    (reading : readScopedExpr? resolve locals term depth = some source.erase)
    (available : ∀ id ∈ definitionRefs roots, ∀ ref,
      resolve id.addr = some ref → (entries ref).isSome = true) : source.ReferencesIn entries := by
  apply (allReferences_erase (fun ref => (entries ref).isSome = true) source).mp
  apply readScopedExpr?_allReferences reading
  intro id reference ref resolved
  exact available id
    (DefinitionReferences.definitionRefs_complete coverage collision member reference) ref resolved

private theorem bind_success {α γ : Type} {action : TcM .anon α}
    {next : α → TcM .anon γ} {before after : TcState .anon} {result : γ}
    (run : EStateM.bind action next before = .ok result after) :
    ∃ value middle, action before = .ok value middle ∧ next value middle = .ok result after := by
  unfold EStateM.bind at run
  cases step : action before with
  | error error state => rw [step] at run; contradiction
  | ok value middle => rw [step] at run; exact ⟨value, middle, rfl, run⟩

/-- Extract the actual dependency traversal from this successful safe
definition's validation, including its final checker state. -/
theorem DefinitionBodyTrace.dependencyOrder {input : DefinitionInput}
    {methods : Methods .anon} {before : TcState .anon}
    (trace : DefinitionBodyTrace input methods before) (safe : input.safety = .safe) :
    ∃ started order,
      (RecM.definitionDependencyOrder input.constant.definitionDependencies).run methods started =
        .ok order trace.validated ∧
      DefinitionDependencies.Certificate (fun _ _ => True)
        input.constant.definitionDependencies order := by
  have validated := trace.validationRun
  unfold RecM.validateConstWellScoped at validated
  change EStateM.bind
    ((RecM.validateExprWellScoped input.type 0 input.universes.toNat).run methods)
    _ before = _ at validated
  obtain ⟨⟨⟩, intermediate, _, rest⟩ := bind_success validated
  change EStateM.bind
    ((RecM.validateExprWellScoped input.value 0 input.universes.toNat).run methods)
    _ intermediate = _ at rest
  obtain ⟨⟨⟩, started, _, checked⟩ := bind_success rest
  change (RecM.checkDefinitionDependencies input.constant).run methods started = _ at checked
  unfold RecM.checkDefinitionDependencies DefinitionInput.constant at checked
  rw [safe] at checked
  change EStateM.bind
    ((RecM.definitionDependencyOrder input.constant.definitionDependencies).run methods)
    _ started = _ at checked
  obtain ⟨order, _, ordered, done⟩ := bind_success checked
  cases done
  exact ⟨started, order, ordered, DefinitionDependencies.order_sound ordered⟩

/-- The collector order supplies all references of the checked body and type
once its entries are resolved in the preceding model interface. Scope and
typing remain the conclusions of their separate production-run theorems. -/
theorem DefinitionBodyTrace.referencesIn {input : DefinitionInput}
    {methods : Methods .anon} {before : TcState .anon}
    (trace : DefinitionBodyTrace input methods before) (safe : input.safety = .safe)
    {resolve : Address → Option (ConstRef β)} {entries : Model.Environment β}
    {body type : AExpr β} {support : RunSupport}
    (typeCoverage : input.type.ValidationCoverage support)
    (valueCoverage : input.value.ValidationCoverage support) (collision : support.CollisionFree)
    (valueReading : readScopedExpr? resolve [] input.value = some body.erase)
    (typeReading : readScopedExpr? resolve [] input.type = some type.erase)
    (available : ∀ started order,
      (RecM.definitionDependencyOrder input.constant.definitionDependencies).run methods started =
        .ok order trace.validated →
      ∀ entry ∈ order, ∀ ref, resolve entry.1.addr = some ref → (entries ref).isSome = true) :
    body.ReferencesIn entries ∧ type.ReferencesIn entries := by
  obtain ⟨started, order, run, certificate⟩ := trace.dependencyOrder safe
  have coverage : ∀ root ∈ [input.type, input.value], root.ValidationCoverage support := by
    intro root member
    rcases List.mem_cons.mp member with rfl | member
    · exact typeCoverage
    · have equality := List.mem_singleton.mp member
      cases equality
      exact valueCoverage
  have present : ∀ id ∈ definitionRefs [input.type, input.value], ∀ ref,
      resolve id.addr = some ref → (entries ref).isSome = true := by
    intro id member ref resolved
    have listed := certificate.covers id member
    obtain ⟨entry, member, equality⟩ := List.mem_map.mp listed
    apply available started order run entry (by simpa using member) ref
    rw [equality]
    exact resolved
  exact ⟨readScopedExpr?_referencesIn coverage collision (by simp) valueReading present,
    readScopedExpr?_referencesIn coverage collision (by simp) typeReading present⟩

end Ix.Kernel.Consistency
