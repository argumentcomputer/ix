import Ix.Cert.SourceUses
import Ix.CompileCert.Loop
import Ix.Compile.SourceContract.Transport

namespace Ix.Cert.SourceInput.Prepared
open Ix.Compile Ix.Compile.SourceInput Ix.CompileCert.Loop

def Named (xs : List Raw) : Prop := ∀ row ∈ xs, row.1 = row.2.name

private theorem named_push {xs : List Raw} {row : Raw}
    (before : Named xs) (named : row.1 = row.2.name) : Named (xs ++ [row]) := by
  intro item member
  rcases List.mem_append.mp member with earlier | last
  · exact before item earlier
  · have same : item = row := by simpa using last
    exact same ▸ named

/-- The existing initial resolve loop already checks every input header.
Later contract/hint processing cannot change the returned constant list. -/
theorem resolve_named {input : CompileInput} {resolved : ResolvedCompileInput}
    (accepted : input.resolve = .ok resolved) :
    Named input.constants ∧ resolved.constants = input.constants := by
  unfold CompileInput.resolve at accepted
  obtain ⟨selected,namesRun,tail⟩ := except_bind_ok.mp accepted
  have named : Named input.constants := by
    refine forIn_inv (fun pre _ => Named pre) _ input.constants ?_
      input.constants [] _ selected rfl (by intro row member; cases member) namesRun
    intro pre row post state result _ before stepped
    rcases row with ⟨name,source⟩
    have same : name = source.name := by
      by_contra different
      simp [different,bind,Except.bind] at stepped
    simp [same,bind,Except.bind,pure,Except.pure] at stepped
    split at stepped
    · cases stepped
    · cases stepped
      exact ⟨_,rfl,named_push before same⟩
  obtain ⟨_,_,tail⟩ := except_bind_ok.mp tail
  obtain ⟨_,_,tail⟩ := except_bind_ok.mp tail
  obtain ⟨_,_,tail⟩ := except_bind_ok.mp tail
  cases tail
  exact ⟨named,rfl⟩

/-- Decoration updates expression fields only; no expression-preservation
claim is needed to establish this existing header frame. -/
theorem decorate_name {contract : ResolvedSourceContract} {out : Lean.ConstantInfo}
    (accepted : contract.decorate = .ok out) : out.name = contract.source.name := by
  unfold ResolvedSourceContract.decorate at accepted
  obtain ⟨type,_,rest⟩ := except_bind_ok.mp accepted
  cases source : contract.source <;> simp only [source] at rest
  all_goals first
    | (obtain ⟨value,_,done⟩ := except_bind_ok.mp rest; cases done; rfl)
    | (cases rest <;> rfl)

private theorem related_origin {α β} {R : α → β → Prop} {xs : List α} {ys : List β}
    (related : List.Forall₂ R xs ys) : ∀ y ∈ ys, ∃ x, x ∈ xs ∧ R x y := by
  induction related with
  | nil => intro y member; cases member
  | @cons x y xs ys head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨x,List.mem_cons_self,head⟩
    · obtain ⟨original,inside,step⟩ := ih value later
      exact ⟨original,List.mem_cons_of_mem _ inside,step⟩

/-- The find? predicate aligns each replacement contract's header with the
tuple; unchanged rows inherit the already checked input header. -/
theorem decorate_named {input : ResolvedCompileInput} {out : List Raw}
    (named : Named input.constants) (accepted : input.decorate = .ok out) : Named out := by
  unfold ResolvedCompileInput.decorate at accepted
  have related := mapM_forall₂ _ accepted
  intro row member
  obtain ⟨original,inside,step⟩ := related_origin related row member
  rcases original with ⟨name,source⟩
  simp only at step
  split at step
  · cases step
  · cases found : input.contracts.find? (·.source.name == name) with
    | none =>
      simp only [found,pure,Except.pure,Except.ok.injEq] at step
      cases step
      exact named _ inside
    | some contract =>
      simp only [found] at step
      obtain ⟨value,decorated,done⟩ := except_bind_ok.mp step
      cases done
      have selected := Array.find?_some
        (p := fun c : ResolvedSourceContract => c.source.name == name) found
      exact (beq_iff_eq.mp selected).symm.trans (decorate_name decorated).symm

/-- Successful preparation itself supplies name/header consistency. -/
theorem prepare_named {input : CompileInput} {raw : List Raw}
    (accepted : input.prepare = .ok raw) : Named raw := by
  unfold CompileInput.prepare at accepted
  obtain ⟨resolved,checked,decorated⟩ := except_bind_ok.mp accepted
  have resolvedRun : input.resolve = .ok resolved := by
    cases run : input.resolve <;> simp [run,Except.mapError] at checked
    exact congrArg Except.ok checked
  obtain ⟨named,frame⟩ := resolve_named resolvedRun
  exact decorate_named (frame ▸ named) decorated

private theorem checked_loop {σ ε : Type} (f : Raw → σ → Except ε (ForInStep σ))
    (live bad : σ → Prop)
    (step : ∀ row state result, live state → f row state = .ok result →
      (∃ next, result = .done next ∧ bad next) ∨
      (∃ next, result = .yield next ∧ live next ∧ row.1 = row.2.name)) :
    ∀ xs state out, live state → forIn xs state f = .ok out → bad out ∨ Named xs := by
  intro xs
  induction xs with
  | nil => intro state out _ _; exact .inr (by intro row member; cases member)
  | cons row xs ih =>
    intro state out alive ran
    rw [List.forIn_cons] at ran
    obtain ⟨result,stepped,rest⟩ := except_bind_ok.mp ran
    rcases step row state result alive stepped with ⟨next,rfl,exited⟩ | ⟨next,rfl,continues,named⟩
    · cases rest; exact .inl exited
    · rcases ih next out continues rest with exited | tail
      · exact .inl exited
      · right; intro value member
        rcases List.mem_cons.mp member with rfl | later
        · exact named
        · exact tail value later

/-- A true ordinary fast-path result cannot have taken a registered early
exit. Therefore its existing loop checked every tuple/header. -/
theorem ordinary_named {constants : List Raw} {registered : Lean.Name → Bool}
    (accepted : checkOrdinaryConstants constants registered = .ok true) : Named constants := by
  unfold checkOrdinaryConstants at accepted
  obtain ⟨state,loop,done⟩ := except_bind_ok.mp accepted
  have result := checked_loop _ (fun state => state.1 = none) (fun state => state.1 = some false)
    (by
      intro row before after alive stepped
      rcases row with ⟨name,source⟩
      have named : name = source.name := by
        by_contra different
        simp [different,bind,Except.bind] at stepped
      simp [named,bind,Except.bind,pure,Except.pure] at stepped
      split at stepped
      · cases stepped
      · split at stepped
        · cases stepped; exact .inl ⟨_,rfl,rfl⟩
        · cases stepped; exact .inr ⟨_,rfl,rfl,named⟩)
    constants _ state rfl loop
  rcases result with exited | named
  · simp [exited,pure,Except.pure] at done
  · exact named

theorem prepareConstants_named {constants raw : List Raw}
    (prepared : prepareSourceConstants constants = .ok raw) : Named raw := by
  unfold prepareSourceConstants at prepared
  obtain ⟨ordinary,checked,rest⟩ := except_bind_ok.mp prepared
  cases ordinary with
  | true => cases rest; exact ordinary_named checked
  | false =>
    obtain ⟨input,_,prepared⟩ := except_bind_ok.mp rest
    exact prepare_named prepared

theorem prepareRegistered_named {env : Lean.Environment} {constants raw : List Raw}
    (prepared : prepareRegisteredConstants env constants = .ok raw) : Named raw := by
  unfold prepareRegisteredConstants at prepared
  obtain ⟨ordinary,checked,rest⟩ := except_bind_ok.mp prepared
  cases ordinary with
  | true => cases rest; exact ordinary_named checked
  | false =>
    obtain ⟨input,_,prepared⟩ := except_bind_ok.mp rest
    exact prepare_named prepared

private def NamedMap (m : Ix.Map Ix.Name Raw) : Prop :=
  ∀ query row, m.get? query = some row → row.1 = row.2.name

private theorem named_fold (xs : List Raw) (named : Named xs)
    (m : Ix.Map Ix.Name Raw) (old : NamedMap m) :
    NamedMap (xs.foldl (fun acc row => acc.insert (Canon.nameS row.1) row) m) := by
  induction xs generalizing m with
  | nil => exact old
  | cons row xs ih =>
    apply ih (fun item member => named item (List.mem_cons_of_mem _ member))
    intro query value stored
    rw [Std.HashMap.get?_eq_getElem?,Std.HashMap.getElem?_insert] at stored
    split at stored
    · cases stored
      exact named row List.mem_cons_self
    · exact old query value (by simpa only [Std.HashMap.get?_eq_getElem?] using stored)

/-- Hash equality only selects a winner; every inserted raw value has the
checked header property. No source-name injectivity hypothesis is used. -/
theorem winner_named {raw : List Raw} (named : Named raw) {query : Ix.Name} {row : Raw}
    (stored : (Ix.Compile.SourceGraph.Prepass.run raw.toArray).leanByIx.get? query = some row) :
    row.1 = row.2.name := by
  rw [SourcePrepass.prepass_raw] at stored
  simp only [SourcePrepass.inserted,SourcePrepass.keyed,List.foldl_map] at stored
  exact named_fold raw named {} (by intro query row h; simp at h) query row stored

private theorem value_of_named {raw : List Raw} (named : Named raw)
    {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).valueAt name = .ok (formOf ci) := by
  obtain ⟨row,winner,_,result⟩ := SourceInput.declared_coverage raw.toArray name ci declared
  have same := winner_named named winner
  simpa only [beq_iff_eq.mpr same,↓reduceIte] using result

/-- A prepared declared input returns its exact original form: the header
refusal is discharged by the actual existing preparation run. -/
theorem prepared_value {input : CompileInput} {raw : List Raw}
    (prepared : input.prepare = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).valueAt name = .ok (formOf ci) :=
  value_of_named (prepare_named prepared) declared

theorem prepared_capture {input : CompileInput} {raw : List Raw}
    (prepared : input.prepare = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).captureUsesAt name = .ok (Uses.capture ci) := by
  unfold Carrier.captureUsesAt
  rw [prepared_value prepared declared]
  rfl

theorem preparedConstants_value {constants raw : List Raw}
    (prepared : prepareSourceConstants constants = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).valueAt name = .ok (formOf ci) :=
  value_of_named (prepareConstants_named prepared) declared

theorem preparedConstants_capture {constants raw : List Raw}
    (prepared : prepareSourceConstants constants = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).captureUsesAt name = .ok (Uses.capture ci) := by
  unfold Carrier.captureUsesAt
  rw [preparedConstants_value prepared declared]
  rfl

theorem preparedRegistered_value {env : Lean.Environment} {constants raw : List Raw}
    (prepared : prepareRegisteredConstants env constants = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).valueAt name = .ok (formOf ci) :=
  value_of_named (prepareRegistered_named prepared) declared

theorem preparedRegistered_capture {env : Lean.Environment} {constants raw : List Raw}
    (prepared : prepareRegisteredConstants env constants = .ok raw) {name : Ix.Name} {ci : Ix.ConstantInfo}
    (declared : (SourceGraph.full (SourceStream.canonical raw.toArray)).consts.get? name = some ci) :
    (ofPrepass (Ix.Compile.SourceGraph.Prepass.run raw.toArray)).captureUsesAt name = .ok (Uses.capture ci) := by
  unfold Carrier.captureUsesAt
  rw [preparedRegistered_value prepared declared]
  rfl

/-- info: 'Ix.Cert.SourceInput.Prepared.prepared_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prepared_value
/-- info: 'Ix.Cert.SourceInput.Prepared.prepared_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms prepared_capture
/-- info: 'Ix.Cert.SourceInput.Prepared.preparedConstants_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms preparedConstants_capture
/-- info: 'Ix.Cert.SourceInput.Prepared.preparedRegistered_capture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms preparedRegistered_capture

end Ix.Cert.SourceInput.Prepared
