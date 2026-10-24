import Ix.Cert.SourcePrepass

/-! Representation correspondence for the actual ChangedSet classifier.
The condensation, table and artifact are fixed arguments. No grounding,
publication enumeration, no-drop or semantic refinement follows here. -/
namespace Ix.Cert.SourceClassifier
open Ix (Name ConstantInfo)
open Ix.Compile.ChangedSet

private def row (p : Name × ConstantInfo) : Option (Address × Array Name) :=
  match p.2 with | .inductInfo v => some (p.1.getHash, v.all) | _ => none
private def rows (env : Ix.Environment) := env.consts.toList.filterMap row

private theorem rows_distinct (env : Ix.Environment) :
    (rows env).Pairwise (fun a b => (a.1 == b.1) = false) := by
  apply List.Pairwise.filterMap row _ env.consts.distinct_keys_toList
  intro a b different p hp q hq
  change (a.1.getHash == b.1.getHash) = false at different
  obtain ⟨n, ci⟩ := a
  obtain ⟨m, cj⟩ := b
  cases ci <;> cases cj <;> simp_all [row]
  simpa only [← hp, ← hq] using different

private theorem leanBlocks_fold (env : Ix.Environment) :
    leanBlocks env = (rows env).foldl (fun m p => m.insert p.1 p.2) {} := by
  unfold leanBlocks rows
  rw [Std.HashMap.fold_eq_foldl_toList, List.foldl_filterMap]
  congr 1
  funext m p
  obtain ⟨n, ci⟩ := p
  cases ci <;> rfl

private theorem ofList_get_iff (xs : List (Address × α))
    (distinct : xs.Pairwise (fun a b => (a.1 == b.1) = false)) (a : Address) (v : α) :
    (Std.HashMap.ofList xs)[a]? = some v ↔ (a, v) ∈ xs := by
  constructor
  · intro found
    have present : (Std.HashMap.ofList xs).contains a = true := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, found]; rfl
    rw [Std.HashMap.contains_ofList, List.contains_iff_exists_mem_beq] at present
    obtain ⟨k, member, same⟩ := present
    obtain ⟨⟨key, value⟩, stored, rfl⟩ := List.mem_map.mp member
    have eq : a = key := by simpa only [beq_iff_eq] using same
    subst key
    have valueAt : (Std.HashMap.ofList xs)[a]? = some value :=
      Std.HashMap.getElem?_ofList_of_mem (BEq.rfl (a := a)) distinct stored
    have eq := Option.some.inj (valueAt.symm.trans found)
    simpa only [eq] using stored
  · intro stored
    exact Std.HashMap.getElem?_ofList_of_mem (BEq.rfl (a := a)) distinct stored

/-- Stored map uniqueness is derived internally; none and some empty remain
distinct, and the complete structural all array is preserved. -/
theorem leanBlocks_get_iff (env : Ix.Environment) (a : Address) (all : Array Name) :
    (leanBlocks env).get? a = some all ↔
      ∃ n v, (n, ConstantInfo.inductInfo v) ∈ env.consts.toList ∧ n.getHash = a ∧ v.all = all := by
  rw [leanBlocks_fold, Std.HashMap.get?_eq_getElem?,
    ← Std.HashMap.Equiv.getElem?_eq Std.HashMap.ofList_equiv_foldl,
    ofList_get_iff _ (rows_distinct env), rows, List.mem_filterMap]
  constructor
  · rintro ⟨⟨n, ci⟩, stored, selected⟩
    cases ci <;> simp only [row] at selected
    all_goals try contradiction
    simp only [Option.some.injEq, Prod.mk.injEq] at selected
    exact ⟨n, _, stored, selected⟩
  · rintro ⟨n, v, stored, rfl, rfl⟩
    exact ⟨(n, .inductInfo v), stored, rfl⟩

theorem leanBlocks_inductives {e₁ e₂ : Ix.Environment}
    (stored : ∀ n v, (n, ConstantInfo.inductInfo v) ∈ e₁.consts.toList ↔
      (n, ConstantInfo.inductInfo v) ∈ e₂.consts.toList) (a : Address) :
    (leanBlocks e₁).get? a = (leanBlocks e₂).get? a := by
  apply Option.ext
  intro all
  simp only [leanBlocks_get_iff, stored]

private theorem componentOf_lookups {l₁ l₂ : Std.HashMap Address (Array Name)}
    (h : ∀ a, l₁.get? a = l₂.get? a) : componentOf l₁ = componentOf l₂ := by
  have get : l₁.get? = l₂.get? := funext h
  funext record
  simp only [componentOf, get]

private theorem changedBlocks_lookups {e₁ e₂ : Ix.Environment}
    (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (lean : ∀ a, (leanBlocks e₁).get? a = (leanBlocks e₂).get? a) (ixe : Ixon.Env) :
    changedBlocks e₁ ixe = changedBlocks e₂ ixe := by
  have get : e₁.get? = e₂.get? := funext lookups
  have source : sourceDefinition e₁ ixe = sourceDefinition e₂ ixe := by
    funext n
    simp only [sourceDefinition, get]
  have component := componentOf_lookups lean
  have definitions : collapsedDefinitionComponents e₁ ixe = collapsedDefinitionComponents e₂ ixe := by
    simp only [collapsedDefinitionComponents, component, source]
  unfold changedBlocks
  dsimp only
  rw [component, definitions]

/-- Reusable representation interface. Its premises are both discharged
from the concrete producer below, not assumptions on a final compile. -/
theorem ofCompile_lookups {e₁ e₂ : Ix.Environment}
    (lookups : ∀ n, e₁.get? n = e₂.get? n)
    (lean : ∀ a, (leanBlocks e₁).get? a = (leanBlocks e₂).get? a)
    (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env) :
    ofCompile e₁ condensed table ixe = ofCompile e₂ condensed table ixe := by
  have get : e₁.get? = e₂.get? := funext lookups
  have blocks := changedBlocks_lookups lookups lean ixe
  have members : Unchanged.memberStage e₁ = Unchanged.memberStage e₂ := by
    funext bs
    simp only [Unchanged.memberStage, get]
  have heads : Unchanged.headStage e₁ = Unchanged.headStage e₂ := by
    funext bs es
    simp only [Unchanged.headStage, get]
  have regenerated : Unchanged.regenStage e₁ = Unchanged.regenStage e₂ := by
    funext t artifact es
    simp only [Unchanged.regenStage, get]
  have tables : cliqueTables e₁ = cliqueTables e₂ := by
    funext bs
    simp only [cliqueTables, get]
  have cliques : cliqueStage e₁ = cliqueStage e₂ := by
    funext bs es
    simp only [cliqueStage, tables]
  simp only [Unchanged.ofCompile_eq, Unchanged.stages, blocks, members, heads, regenerated, cliques]

theorem produced_leanBlocks (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (a : Address) :
    (leanBlocks (Hybrid.hybridEnv (Ix.Compile.SourceGraph.Prepass.produce reserved raw workers).2.facts.code
      (Ix.Compile.SourceGraph.Prepass.run raw).leanByIx)).get? a =
    (leanBlocks (SourceGraph.full (SourceStream.canonical raw))).get? a :=
  leanBlocks_inductives (SourcePrepass.stored_inductives reserved raw workers) a

/-- Literal whole-classifier equality at the SAME condensation/table/artifact.
The stored inductive and lookup facts come from the actual producer. -/
theorem produced_ofCompile (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (condensed : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env) :
    ofCompile (Hybrid.hybridEnv (Ix.Compile.SourceGraph.Prepass.produce reserved raw workers).2.facts.code
      (Ix.Compile.SourceGraph.Prepass.run raw).leanByIx) condensed table ixe =
    ofCompile (SourceGraph.full (SourceStream.canonical raw)) condensed table ixe :=
  ofCompile_lookups (SourcePrepass.produced_hybrid_lookup reserved raw workers)
    (produced_leanBlocks reserved raw workers) condensed table ixe

end Ix.Cert.SourceClassifier
