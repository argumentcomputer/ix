import Ix.Cert.SourcePrepass
import Ix.Cert.SourceOrder.Map

/-! Actual Node/full-map enumeration from the same insertion trace. No
arbitrary HashMap-equivalence, key permutation or publication premise. -/
namespace Ix.Cert.SourceOrder
open Ix (Name ConstantInfo)
open Ix.Compile.SourceGraph

private theorem nodes_fold (rows : List (Name × ConstantInfo)) (acc : Collected) :
    ((rows.map fun (n, ci) => rowOfCanonical n ci).foldl mergeRow acc).nodes =
      rows.foldl (fun m p => m.insert p.1 (capture p.2)) acc.nodes := by
  induction rows generalizing acc with
  | nil => rfl
  | cons p rows ih =>
    rw [List.map_cons, List.foldl_cons, ih, List.foldl_cons]
    cases acc
    rfl

/-- Structural stored keys in literal order, through replacements/resizes. -/
theorem collected_keys (rows : List (Name × ConstantInfo)) :
    (collect (rows.map fun (n, ci) => rowOfCanonical n ci)).nodes.toList.map (·.1) =
      (SourceGraph.full rows).consts.toList.map (·.1) := by
  unfold collect
  rw [nodes_fold]
  exact Map.inserted_keys rows capture

theorem produced_keys (reserved : Lean.ConstantInfo → Bool) (raw : Array SourcePrepass.Raw) (workers : Nat) :
    (Prepass.produce reserved raw workers).2.facts.nodes.toList.map (·.1) =
      (SourceGraph.full (SourceStream.canonical raw)).consts.toList.map (·.1) := by
  rw [SourcePrepass.produced_facts]
  exact collected_keys _

end Ix.Cert.SourceOrder
