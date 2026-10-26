import Ix.Compile.SourceInput.GroupView
import Ix.Cert.SourceInput.Prepared
import Ix.Cert.SourceOrder.Map
import IxC.Kernel.Audit.Axioms

namespace Ix.Cert.SourceGroupView
open Ix.Compile.SourceInput Ix.Compile.SourceInput.GroupView Ix.CompileCert.Loop

theorem project_header (ci : Ix.ConstantInfo) : (project ci).headerName = ci.getCnst.name := rfl

theorem project_inductive (d : Ix.InductiveVal) :
    project (.inductInfo d) = ⟨d.cnst.name,.inductiveDecl d.all d.ctors d.numNested⟩ := rfl
theorem project_constructor (d : Ix.ConstructorVal) :
    project (.ctorInfo d) = ⟨d.cnst.name,.constructorDecl d.induct d.cidx⟩ := rfl
theorem project_recursor (d : Ix.RecursorVal) :
    project (.recInfo d) = ⟨d.cnst.name,.recursorDecl d.all⟩ := rfl

/-- Exact key order through the actual raw/canonical insertion traces,
including replacement and resizing. Lookup equivalence is not used. -/
theorem produced_keys (raw : Array Raw) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw)).groupKeys =
      (SourceGraph.full (SourceStream.canonical raw)).consts.toList.map Prod.fst := by
  simp only [Carrier.groupKeys,ofPrepass,SourcePrepass.prepass_raw]
  have ordered := SourceOrder.Map.inserted_keys (SourcePrepass.keyed raw)
    (fun row : Raw => Canon.constS row.2)
  simpa only [SourcePrepass.inserted,SourcePrepass.keyed,SourceGraph.full,
    SourceStream.canonical,List.map_map,List.foldl_map,Function.comp_def] using ordered.symm

/-- An enumerated stored key has its actual raw winner, even without a
lawful structural BEq on Ix.Name or a name/hash injectivity hypothesis. -/
theorem key_has_winner {carrier : Carrier} {name : Ix.Name} (present : name ∈ carrier.groupKeys) :
    ∃ raw, carrier.byName.get? name = some raw := by
  obtain ⟨⟨key,raw⟩,member,same⟩ := List.mem_map.mp present
  dsimp only at same
  subst key
  exact ⟨raw,(Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp member).2⟩

theorem row_of_value {carrier : Carrier} {name : Ix.Name} {form : Form}
    (value : carrier.valueAt name = .ok form) :
    carrier.groupRowAt name = .ok ⟨name,project form.original⟩ := by
  simp only [Carrier.groupRowAt,Carrier.groupMetaAt,value,Functor.map,Except.map]

/-- Literal original-value provenance for one output row; the stored key
is not silently replaced by the header name or a pretty-name representative. -/
theorem row_origin {carrier : Carrier} {name : Ix.Name} {row : Row}
    (accepted : carrier.groupRowAt name = .ok row) :
    row.storedKey = name ∧ ∃ raw, carrier.byName.get? name = some raw ∧
      raw.1 = raw.2.name ∧ row.grouping = project (Canon.constS raw.2) := by
  cases value : carrier.valueAt name with
  | error e =>
    simp only [Carrier.groupRowAt,Carrier.groupMetaAt,value,Functor.map,Except.map] at accepted
    cases accepted
  | ok form =>
    have same : (⟨name,project form.original⟩ : Row) = row := by
      simpa only [Carrier.groupRowAt,Carrier.groupMetaAt,value,Functor.map,Except.map,Except.ok.injEq]
        using accepted
    subst row
    obtain ⟨raw,winner,named,origin⟩ := SourceInput.valueAt_origin value
    exact ⟨rfl,raw,winner,named,by rw [origin]; rfl⟩

/-- Every enumerated key has exactly one corresponding output row, in the
same position, with its own successful original lookup and full projection. -/
theorem view_sound {carrier : Carrier} {rows : List Row}
    (accepted : carrier.groupView = .ok rows) :
    List.Forall₂ (fun name row => row.storedKey = name ∧ ∃ raw,
      carrier.byName.get? name = some raw ∧ raw.1 = raw.2.name ∧
      row.grouping = project (Canon.constS raw.2)) carrier.groupKeys rows := by
  have runs := mapM_forall₂ carrier.groupRowAt accepted
  clear accepted
  generalize carrier.groupKeys = keys at runs ⊢
  induction runs with
  | nil => exact .nil
  | cons head _ ih => exact .cons (row_origin head) ih

theorem view_keys {carrier : Carrier} {rows : List Row} (accepted : carrier.groupView = .ok rows) :
    rows.map Row.storedKey = carrier.groupKeys := by
  have sound := view_sound accepted
  clear accepted
  generalize carrier.groupKeys = keys at sound ⊢
  induction sound with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons,head.1,ih]

theorem view_length {carrier : Carrier} {rows : List Row} (accepted : carrier.groupView = .ok rows) :
    rows.length = carrier.byName.size := by
  have length := congrArg List.length (view_keys accepted)
  simpa [Carrier.groupKeys] using length

private theorem view_of_values (carrier : Carrier) (pairs : List (Ix.Name × Ix.ConstantInfo))
    (keys : carrier.groupKeys = pairs.map Prod.fst)
    (values : ∀ pair ∈ pairs, carrier.valueAt pair.1 = .ok (formOf pair.2)) :
    carrier.groupView = .ok (pairs.map fun (key,ci) => ⟨key,project ci⟩) := by
  unfold Carrier.groupView
  rw [keys]
  clear keys
  revert values
  induction pairs with
  | nil => intro _; rfl
  | cons pair pairs ih =>
    intro values
    simp only [List.map_cons,List.mapM_cons]
    rw [row_of_value (values pair List.mem_cons_self)]
    have tail := ih (fun p member => values p (List.mem_cons_of_mem _ member))
    simp only [bind,Except.bind,tail,pure,Except.pure]
    rfl

/-- The full map is a SEMANTIC specification here, not a runtime allocation.
Complete declared lookup totality and exact insertion order determine the
entire output list, including each metadata value and its stored key. -/
private theorem view_of_declared (raw : Array Raw)
    (values : ∀ name ci,
      (SourceGraph.full (SourceStream.canonical raw)).consts.get? name = some ci →
      (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw)).valueAt name = .ok (formOf ci)) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw)).groupView =
      .ok ((SourceGraph.full (SourceStream.canonical raw)).consts.toList.map
        fun (key,ci) => ⟨key,project ci⟩) := by
  apply view_of_values _ _ (produced_keys raw)
  intro pair member
  exact values pair.1 pair.2
    (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp member).2

/-- Every original winner of the actual prepared input is projected. The
conclusion has no missing/header-refusal alternative or new input restriction. -/
theorem prepared_view {input : Ix.Compile.CompileInput} {raw : List Raw}
    (prepared : input.prepare = .ok raw) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).groupView =
      .ok ((SourceGraph.full (SourceStream.canonical raw.toArray)).consts.toList.map
        fun (key,ci) => ⟨key,project ci⟩) :=
  view_of_declared _ (fun _ _ declared => SourceInput.Prepared.prepared_value prepared declared)

theorem preparedConstants_view {constants raw : List Raw}
    (prepared : Ix.Compile.prepareSourceConstants constants = .ok raw) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).groupView =
      .ok ((SourceGraph.full (SourceStream.canonical raw.toArray)).consts.toList.map
        fun (key,ci) => ⟨key,project ci⟩) :=
  view_of_declared _ (fun _ _ declared => SourceInput.Prepared.preparedConstants_value prepared declared)

theorem preparedRegistered_view {env : Lean.Environment} {constants raw : List Raw}
    (prepared : Ix.Compile.prepareRegisteredConstants env constants = .ok raw) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).groupView =
      .ok ((SourceGraph.full (SourceStream.canonical raw.toArray)).consts.toList.map
        fun (key,ci) => ⟨key,project ci⟩) :=
  view_of_declared _ (fun _ _ declared => SourceInput.Prepared.preparedRegistered_value prepared declared)

#guard_kernel_axioms produced_keys [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms key_has_winner [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms row_origin [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms view_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms view_keys [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms view_length [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms prepared_view [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms preparedConstants_view [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms preparedRegistered_view [propext, Classical.choice, Quot.sound]

end Ix.Cert.SourceGroupView
