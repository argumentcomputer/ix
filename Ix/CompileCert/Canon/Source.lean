module
public import Ix.Compile.Canon.Source
import all Ix.Compile.Canon.Source
public import Ix.Environment
import all Ix.Environment
public import Ix.Compile.Canon.Nested
import all Ix.Compile.Canon.Nested
public section

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name ConstantInfo)

open Ix.Compile.Canon

/-- Inductive views retain the query key, even if the source record stores
a different declaration name. This is the registry lookup used by expansion. -/
theorem IndView.query_name (lookup : Ix.Name → Option Ix.ConstantInfo)
    {n : Ix.Name} {v : IndView} (h : IndView.ofConst? lookup n = some v) : v.name = n := by
  unfold IndView.ofConst? at h
  split at h
  · cases h; rfl
  · cases h

set_option maxRecDepth 10000 in
theorem collectSource_protected_mono (source : Ix.Environment) (refs : Ix.ConstantInfo → List Ix.Name)
    (names : Ix.ConstantInfo → List Lean.Name) (pending : List Ix.Name)
    (out : SourceContext) (groups : Std.HashMap Ix.Name (Array (Array Ix.Name))) :
    out.protectedNames ⊆ (collectSource source refs names pending out groups).protectedNames := by
  fun_induction collectSource source refs names pending out groups
  all_goals first
    | exact List.Subset.refl _
    | intro n hn
      apply_assumption
      first
      | exact List.mem_cons_of_mem _ hn
      | exact List.mem_append_right _ (List.mem_cons_of_mem _ hn)

set_option maxRecDepth 10000 in
theorem collectSource_pending_protected (source : Ix.Environment) (refs : Ix.ConstantInfo → List Ix.Name)
    (names : Ix.ConstantInfo → List Lean.Name) (pending : List Ix.Name)
    (out : SourceContext) (groups : Std.HashMap Ix.Name (Array (Array Ix.Name))) :
    ∀ n ∈ pending, keyName n ∈ (collectSource source refs names pending out groups).protectedNames := by
  fun_induction collectSource source refs names pending out groups
  · simp
  all_goals
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · apply collectSource_protected_mono
      first
      | exact List.mem_cons_self
      | exact List.mem_append_right _ List.mem_cons_self
    · apply_assumption
      first | exact hn | exact List.mem_append_right _ hn



theorem source_map_key_eq {α : Type} (map : Std.HashMap Name α) {a b : Name}
    (h : a.getHash = b.getHash) : map.get? a = map.get? b := by
  change map[a]? = map[b]?
  apply Std.HashMap.getElem?_congr
  change (a.getHash == b.getHash) = true
  rw [h]
  exact BEq.rfl

theorem source_get_key_eq (source : Ix.Environment) {a b : Name}
    (h : a.getHash = b.getHash) : source.get? a = source.get? b := by
  unfold Ix.Environment.get?
  rw [source_map_key_eq source.overlay h, source_map_key_eq source.consts h]
  cases source.overlay.get? b with
  | some value => rfl
  | none =>
    cases source.consts.get? b with
    | some value => rfl
    | none =>
      cases source.fallback? with
      | none => rfl
      | some f => simp only [Ix.LazyConstants.get?, source_map_key_eq f.index h]

def sourceEdges (refs : ConstantInfo → List Name)
    (groups : Std.HashMap Name (Array (Array Name))) (n : Name) (ci : ConstantInfo) : List Name :=
  refs ci ++ match ci with
  | .inductInfo _ => ((groups.get? n).getD #[]).toList.flatMap (·.toList)
  | _ => []

theorem sourceEdges_key_eq (refs : ConstantInfo → List Name)
    (groups : Std.HashMap Name (Array (Array Name))) {a b : Name}
    (h : a.getHash = b.getHash) (ci : ConstantInfo) :
    sourceEdges refs groups a ci = sourceEdges refs groups b ci := by
  cases ci <;> simp only [sourceEdges]
  rw [show groups.get? a = groups.get? b from source_map_key_eq groups h]

/-- A query spelling is protected, and either its record is unavailable or
its actual finite-map lookup identity has been visited. -/
def SourceDone (source : Ix.Environment) (out : SourceContext) (n : Name) : Prop :=
  keyName n ∈ out.protectedNames ∧ (source.get? n = none ∨ n.getHash ∈ out.visitedKeys)

set_option maxRecDepth 10000 in
theorem collectSource_visited_mono (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name)
    (out : SourceContext) (groups : Std.HashMap Name (Array (Array Name))) :
    out.visitedKeys ⊆ (collectSource source refs names pending out groups).visitedKeys := by
  fun_induction collectSource source refs names pending out groups
  all_goals first
    | exact List.Subset.refl _
    | intro n hn
      apply_assumption
      first | exact hn | exact List.mem_cons_of_mem _ hn

set_option maxRecDepth 10000 in
theorem collectSource_pending_done (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name)
    (out : SourceContext) (groups : Std.HashMap Name (Array (Array Name))) :
    ∀ n ∈ pending, SourceDone source (collectSource source refs names pending out groups) n := by
  fun_induction collectSource source refs names pending out groups
  · simp
  all_goals
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · constructor
      · apply collectSource_protected_mono
        first | exact List.mem_cons_self | exact List.mem_append_right _ List.mem_cons_self
      · first
        | exact Or.inl (by assumption)
        | apply Or.inr
          apply collectSource_visited_mono
          first | assumption | exact List.mem_cons_self
    · apply_assumption
      first | exact hn | exact List.mem_append_right _ hn

set_option maxRecDepth 10000 in
theorem collectSource_visited_info (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name)
    (out : SourceContext) (groups : Std.HashMap Name (Array (Array Name))) :
    ∀ n ci, n.getHash ∈ (collectSource source refs names pending out groups).visitedKeys →
      source.get? n = some ci → n.getHash ∈ out.visitedKeys ∨
      (names ci ⊆ (collectSource source refs names pending out groups).protectedNames ∧
        ∀ r ∈ sourceEdges refs groups n ci,
          SourceDone source (collectSource source refs names pending out groups) r) := by
  fun_induction collectSource source refs names pending out groups
  · intro n ci hn _; exact .inl hn
  case case2 out head rest out1 hsrc ih => exact ih
  case case3 out head rest out1 value hsrc out2 known ih => exact ih
  case case4 out head rest out1 value hsrc out2 fresh groupRefs ih =>
    intro n ci hn hget
    rcases ih n ci hn hget with hold | hnew
    · rcases List.mem_cons.mp hold with same | hold
      · right
        have lookup := source_get_key_eq source same
        rw [hget, hsrc] at lookup
        have hc : ci = value := Option.some.inj lookup
        subst ci
        constructor
        · intro field hf
          apply collectSource_protected_mono
          exact List.mem_append_left _ hf
        · intro r hr
          apply collectSource_pending_done
          apply List.mem_append_left rest
          have he : sourceEdges refs groups n value = refs value ++ groupRefs := by
            rw [sourceEdges_key_eq refs groups same]
            cases value <;> rfl
          rw [he] at hr
          exact hr
      · exact .inl hold
    · exact .inr hnew

/-- Actual declaration/reference and compiled-registry reachability from
this block. Missing records terminate an edge; they never invent a body. -/
inductive SourceReach (source : Ix.Environment)
    (groups : Std.HashMap Name (Array (Array Name))) (seeds : List Name) : Name → Prop
  | seed {n : Name} : n ∈ seeds → SourceReach source groups seeds n
  | edge {n r : Name} {ci : ConstantInfo} :
      SourceReach source groups seeds n → source.get? n = some ci →
      r ∈ sourceEdges sourceConstRefs groups n ci → SourceReach source groups seeds r

/-- Every successfully visited lookup has all fields protected and every
actual outgoing edge processed. The initial state contributes no hypothesis. -/
theorem sourceContext_closed (source : Ix.Environment) (members : Array Name)
    (groups : Std.HashMap Name (Array (Array Name))) {n : Name} {ci : ConstantInfo}
    (hv : n.getHash ∈ (sourceContext source members groups).visitedKeys)
    (hg : source.get? n = some ci) :
    sourceConstNames ci ⊆ (sourceContext source members groups).protectedNames ∧
      ∀ r ∈ sourceEdges sourceConstRefs groups n ci,
        SourceDone source (sourceContext source members groups) r := by
  have result := collectSource_visited_info source sourceConstRefs sourceConstNames
    members.toList {} groups n ci hv hg
  rcases result with impossible | result
  · cases impossible
  · exact result

/-- Every query in the complete block-reachable closure is protected and
processed, without a caller completeness or cardinality premise. -/
theorem sourceContext_reachable_done (source : Ix.Environment) (members : Array Name)
    (groups : Std.HashMap Name (Array (Array Name))) {n : Name}
    (hr : SourceReach source groups members.toList n) :
    SourceDone source (sourceContext source members groups) n := by
  induction hr with
  | seed member =>
    exact collectSource_pending_done source sourceConstRefs sourceConstNames
      members.toList {} groups _ member
  | edge reach lookup edge ih =>
    rcases ih.2 with missing | visited
    · rw [lookup] at missing; cases missing
    · exact (sourceContext_closed source members groups visited lookup).2 _ edge

/-- All typed name fields of every reachable record are forbidden, including
its metadata, binders and universe parameters. -/
theorem sourceContext_reachable_names (source : Ix.Environment) (members : Array Name)
    (groups : Std.HashMap Name (Array (Array Name))) {n : Name} {ci : ConstantInfo}
    (hr : SourceReach source groups members.toList n) (hg : source.get? n = some ci) :
    sourceConstNames ci ⊆ (sourceContext source members groups).protectedNames := by
  rcases (sourceContext_reachable_done source members groups hr).2 with missing | visited
  · rw [hg] at missing; cases missing
  · exact (sourceContext_closed source members groups visited hg).1

end Ix.CompileCert.Canon
