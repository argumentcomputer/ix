import Ix.Cert.SourceOrder
import Ix.Cert.SourceSummaryReverse
import Ix.Cert.SourceClassifier

/-! Unwired publication adapter for sub = the complete prepared input E.
No arbitrary closure enumeration, grounding, no-drop or admission claim. -/
namespace Ix.Cert.SourcePublication
open Ix (Name)
open Ix.Compile.SourceGraph

def published? (nodes : Ix.Map Name Node) (ixe : Ixon.Env) (n : Name) : Option Address :=
  if nodes.contains n then (ixe.named.get? n).map (·.addr) else none
def rowPublished? (nodes : Ix.Map Name Node) (ixe : Ixon.Env) (n : Name) : Option Address :=
  if nodes.contains n then (ixe.named.get? (Ix.Compile.Pass.Clique.rowName n)).map (·.addr) else none

/-- Direct/row source names are the original entry names, not getKey?
representatives. Cascades use actual node-key enumeration without sorting. -/
def selectOriginal (nodes : Ix.Map Name Node) (cs : Ix.Compile.ChangedSet.ChangedSet)
    (ixe : Ixon.Env) : List SelectedRoots.Root :=
  let seen := (SourceReverse.walk (Reverse.build nodes) cs.names).seen
  (cs.entries.toList.filterMap fun e =>
    (published? nodes ixe e.name).map fun a => ⟨e.name, a, .direct e.cause⟩) ++
    ((nodes.toList.map (·.1)).filterMap fun n =>
      if cs.contains n = false ∧ seen.contains n = true then
        (published? nodes ixe n).map fun a => ⟨n, a, .cascade⟩
      else none) ++
    (cs.entries.toList.filterMap fun e =>
      if e.cause = .clique then
        (rowPublished? nodes ixe e.name).map fun a => ⟨e.name, a, .row⟩ else none)

private theorem domain (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (n : Name) :
    (Prepass.produce reserved raw workers).2.facts.nodes.contains n =
      (SourceGraph.full (SourceStream.canonical raw)).consts.contains n := by
  rw [SourcePrepass.produced_facts, Std.HashMap.contains_eq_isSome_getElem?,
    Std.HashMap.contains_eq_isSome_getElem?]
  change ((collect _).nodes.get? n).isSome = _
  rw [SourceGraph.collect_nodes_get]
  simp

private theorem published_eq {nodes : Ix.Map Name Node} {env : Ix.Environment}
    (h : ∀ n, nodes.contains n = env.consts.contains n) (ixe : Ixon.Env) (n : Name) :
    published? nodes ixe n = SelectedRoots.published? env ixe n := by
  unfold published? SelectedRoots.published?
  rw [h n, Std.HashMap.contains_eq_isSome_getElem?]
  change (if (env.consts.get? n).isSome then _ else _) = _
  cases env.consts.get? n <;> cases ixe.named.get? n <;> rfl

private theorem rowPublished_eq {nodes : Ix.Map Name Node} {env : Ix.Environment}
    (h : ∀ n, nodes.contains n = env.consts.contains n) (ixe : Ixon.Env) (n : Name) :
    rowPublished? nodes ixe n = SelectedRoots.rowPublished? env ixe n := by
  unfold rowPublished? SelectedRoots.rowPublished?
  rw [h n, Std.HashMap.contains_eq_isSome_getElem?]
  change (if (env.consts.get? n).isSome then _ else _) = _
  cases env.consts.get? n <;> cases ixe.named.get? (Ix.Compile.Pass.Clique.rowName n) <;> rfl

/-- Literal complete ordered roots/reasons at sub = E, the original domain. -/
theorem selectOriginal_produced (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (cs : Ix.Compile.ChangedSet.ChangedSet) (ixe : Ixon.Env) :
    selectOriginal (Prepass.produce reserved raw workers).2.facts.nodes cs ixe =
      SelectedRoots.select (SourceGraph.full (SourceStream.canonical raw)) cs
        (SourceGraph.full (SourceStream.canonical raw)) ixe := by
  simp only [selectOriginal, SelectedRoots.select, SelectedRoots.directRoots, SelectedRoots.cascadeRoots,
    SelectedRoots.rowRoots, published_eq (domain reserved raw workers), rowPublished_eq (domain reserved raw workers),
    SourceOrder.produced_keys, SourceSummaryReverse.produced_affected, List.filterMap_map, Function.comp_def]

/-- The actual hybrid classifier is transported at the SAME blocks/table/ixe;
no live grounding/table/refusal-history or publication completeness follows. -/
theorem selectCompile_produced (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw)
    (workers : Nat) (blocks : Ix.CondensedBlocks) (table : Ix.AuxGen.AuxTable) (ixe : Ixon.Env) :
    selectOriginal (Prepass.produce reserved raw workers).2.facts.nodes
      (Ix.Compile.ChangedSet.ofCompile (Hybrid.hybridEnv (Prepass.produce reserved raw workers).2.facts.code
        (Prepass.run raw).leanByIx) blocks table ixe) ixe =
      SelectedRoots.selectCompile (SourceGraph.full (SourceStream.canonical raw)) blocks table
        (SourceGraph.full (SourceStream.canonical raw)) ixe := by
  rw [SourceClassifier.produced_ofCompile, selectOriginal_produced]
  rfl

end Ix.Cert.SourcePublication
