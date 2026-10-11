import Ix.CompileCert.Canon.SourceScopes

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

theorem RefScope.getAppFnArgs {P : Name → Prop} {e : Expr} (h : RefScope P e) :
    RefScope P (Ix.Compile.Canon.getAppFnArgs e).1 ∧ ∀ a ∈ (Ix.Compile.Canon.getAppFnArgs e).2, RefScope P a := by
  induction e with
  | app f a hash ihf _ =>
    have parts : RefScope P f ∧ RefScope P a := by
      simpa [RefScope, sourceExprRefs, or_imp, forall_and] using h
    obtain ⟨head,args⟩ := ihf parts.1
    refine ⟨head, ?_⟩
    intro x hx
    have member : x ∈ (Ix.Compile.Canon.getAppFnArgs f).2 ∨ x = a := by simpa [Ix.Compile.Canon.getAppFnArgs] using hx
    rcases member with old | rfl
    · exact args x old
    · exact parts.2
  | _ => exact ⟨h, by simp [Ix.Compile.Canon.getAppFnArgs]⟩

theorem RefScope.mkAppN {P : Name → Prop} {head : Expr} (hh : RefScope P head)
    {args : Array Expr} (ha : ∀ a ∈ args, RefScope P a) : RefScope P (Ix.Compile.Canon.mkAppN head args) := by
  unfold Ix.Compile.Canon.mkAppN
  rw [← Array.foldl_toList]
  suffices ∀ (xs : List Expr), (∀ a ∈ xs, RefScope P a) → ∀ head,
      RefScope P head → RefScope P (xs.foldl Expr.mkApp head) by
    exact this args.toList (by simpa using ha) head hh
  intro xs
  induction xs with
  | nil => intro _ head hh; exact hh
  | cons a xs ih =>
    intro ha head hh
    apply ih
    · intro x hx; exact ha x (List.mem_cons_of_mem _ hx)
    · simpa [RefScope, sourceExprRefs, or_imp, forall_and] using And.intro hh (ha a List.mem_cons_self)

theorem SourceReach.inductive_member {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {seeds : List Name}
    {n : Name} {v : Ix.InductiveVal} (hr : SourceReach source groups seeds n)
    (hget : source.get? n = some (.inductInfo v)) {m : Name} (hm : m ∈ v.all) :
    SourceReach source groups seeds m := by
  apply SourceReach.edge hr hget
  simp only [sourceEdges, sourceConstRefs, List.mem_append, Array.mem_toList_iff]
  exact Or.inl (Or.inr (Or.inl hm))

theorem SourceReach.constructor {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {seeds : List Name}
    {n : Name} {v : Ix.InductiveVal} (hr : SourceReach source groups seeds n)
    (hget : source.get? n = some (.inductInfo v)) {c : Name} (hc : c ∈ v.ctors) :
    SourceReach source groups seeds c := by
  apply SourceReach.edge hr hget
  simp only [sourceEdges, sourceConstRefs, List.mem_append, Array.mem_toList_iff]
  exact Or.inl (Or.inr (Or.inr hc))

/-- The view's type, universe context and mutual-members field come from
exactly the resolved record; its own name remains the query spelling. -/
theorem IndView.sourceInfo {source : Ix.Environment} {n : Name} {view : IndView}
    (hv : IndView.ofConst? source.get? n = some view) :
    ∃ v, source.get? n = some (.inductInfo v) ∧ view.name = n ∧
      view.type = v.cnst.type ∧ view.levelParams = v.cnst.levelParams ∧ view.all = v.all := by
  unfold IndView.ofConst? at hv
  split at hv
  · rename_i v hn
    cases hv
    exact ⟨v,hn,rfl,rfl,rfl,rfl⟩
  · cases hv

theorem SourceReach.registry_member {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {seeds : List Name}
    {n : Name} {v : Ix.InductiveVal} (hr : SourceReach source groups seeds n)
    (hget : source.get? n = some (.inductInfo v)) {classes : Array (Array Name)}
    (registered : groups.get? n = some classes) {cls : Array Name} (hcls : cls ∈ classes)
    {member : Name} (hm : member ∈ cls) : SourceReach source groups seeds member := by
  apply SourceReach.edge hr hget
  unfold sourceEdges
  apply List.mem_append_right
  simp only [registered, Option.getD_some]
  apply List.mem_flatMap.mpr
  exact ⟨cls, by simpa using hcls, by simpa using hm⟩

/-- Every external class actually opened by SourceGroups is in the collected
closure: either the actual registry edge, or the source record's all field. -/
theorem SourceReach.groupMember {source : Ix.Environment}
    {groups : SourceGroups} {seeds : List Name} {n : Name} {view : IndView}
    (hr : SourceReach source groups.blocks seeds n)
    (hv : IndView.ofConst? source.get? n = some view)
    {cls : Array Name} (hcls : cls ∈ groups view) {member : Name} (hm : member ∈ cls) :
    SourceReach source groups.blocks seeds member := by
  obtain ⟨v,hget,hname,-,-,hall⟩ := IndView.sourceInfo hv
  unfold SourceGroups.apply blockGroup at hcls
  rw [hname] at hcls
  cases registered : groups.blocks.get? n with
  | some classes =>
    rw [registered] at hcls
    exact hr.registry_member hget registered (Array.mem_filter.mp hcls).1 hm
  | none =>
    rw [registered] at hcls
    obtain ⟨original,memberAll,equal⟩ := Array.mem_map.mp hcls
    subst cls
    have same : member = original := by simpa using hm
    subst member
    apply hr.inductive_member hget
    simpa [hall] using memberAll

theorem IndView.sourceCtor {source : Ix.Environment} {n : Name} {view : IndView}
    (hv : IndView.ofConst? source.get? n = some view) {ctor : Name × Expr × Nat}
    (hc : ctor ∈ view.ctors) :
    ∃ v cv, source.get? n = some (.inductInfo v) ∧ ctor.1 ∈ v.ctors ∧
      source.get? ctor.1 = some (.ctorInfo cv) ∧ ctor.2.1 = cv.cnst.type := by
  unfold IndView.ofConst? at hv
  split at hv
  · rename_i v hn
    cases hv
    obtain ⟨cn,member,hcn⟩ := Array.mem_filterMap.mp hc
    split at hcn
    · rename_i cv hcv
      cases hcn
      exact ⟨v,cv,hn,member,hcv,rfl⟩
    · cases hcn
  · cases hv

/-- Each constructor actually returned by the production view is a reached
source read, and both its expression references and its query spelling are
covered by the finite closure. No constructor-prefix or caller completeness
assumption is needed. -/
theorem SourceReach.viewCtor {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {members : Array Name}
    {n : Name} {view : IndView} (hr : SourceReach source groups members.toList n)
    (hv : IndView.ofConst? source.get? n = some view) {ctor : Name × Expr × Nat}
    (hc : ctor ∈ view.ctors) :
    SourceReach source groups members.toList ctor.1 ∧
      RefScope (SourceReach source groups members.toList) ctor.2.1 ∧
      keyName ctor.1 ∈ (sourceContext source members groups).protectedNames := by
  obtain ⟨v,cv,hget,member,hctor,htype⟩ := IndView.sourceCtor hv hc
  have reached := hr.constructor hget member
  refine ⟨reached, ?_, (sourceContext_reachable_done source members groups reached).1⟩
  rw [htype]
  exact reached.type_scope hctor

end Ix.CompileCert.Canon
