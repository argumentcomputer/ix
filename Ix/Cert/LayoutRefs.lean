import Ix.Cert.ClosureLayout
import Ix.Cert.GroupRefs

/-! # `Layout.refs` from the compile's references

`ClosureLayout.Layout.refs` asks that a stored reference of a record of a group's name be the
published address of a name of the group or of a group it references (`Graph.hard`). This
module splits it into the compile's side and quotient Source's graph: the compile's side
(`CompiledRefs`) says that such a reference is the published address of a constant that a name
of the group references in the closure's grounded reference graph, outside that name's strongly
connected component (the compile's block); quotient Source's graph puts every such constant in
the group or a group it references (`GroupRefs.refs_in_hard`), up to the names' hash, which
publishes alike (`layoutRefs_of_compiled`). -/

namespace Ix.Cert.LayoutRefs

open Ix.LeanIngress (Graph Group FiberMap graphCollapsed scheduleOf)
open Ix.Cert.ClosureLayout

/-- **The compile's side of `Layout.refs`**: a stored reference of a record of a group's name is
the published address of a constant that a name of the group references in the closure's
grounded reference graph, outside that name's component. -/
def CompiledRefs (ixe : Ixon.Env) (sub : Ix.Environment) (g : Graph) : Prop :=
  ∀ (i : Nat) (gr : Group), g.groups[i]? = some gr → ∀ n ∈ gr.names, ∀ a ∈ nameRecords ixe n, ∀ c,
    recordAt ixe a = some c → ∀ r ∈ c.refs, ixe.consts.contains r = true →
      ∃ n' ∈ gr.names, ∃ m, addrOf ixe m = some r ∧ ((groundedRefs sub).getD n' {}).contains m = true ∧
        ∀ lo all, (blocksOf sub).lowLinks.get? n' = some lo → (blocksOf sub).blocks.get? lo = some all →
          all.contains m = false

/-- Names that hash alike are published alike. -/
theorem addrOf_congr {ixe : Ixon.Env} {k m : Ix.Name} (h : (k == m) = true) : addrOf ixe k = addrOf ixe m := by
  unfold addrOf
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr h]

/-- **`Layout.refs` from the compile's references**, for a graph whose every scheduled group the
schedule lets through. -/
theorem layoutRefs_of_compiled {ρ : FiberMap}
    {hints : Ix.Kernel.Reader.CName .source → Option Ix.Kernel.ReducibilityHint} {ixe : Ixon.Env}
    {sub : Ix.Environment}
    (scheduled : ∀ x ∈ (scheduleOf (graphCollapsed ρ hints sub (blocksOf sub))).zipIdx.toList,
      ∃ conv, x.1.2 = .ok conv)
    (compiled : CompiledRefs ixe sub (graphCollapsed ρ hints sub (blocksOf sub))) :
    ∀ (i : Nat) (gr : Group), (graphCollapsed ρ hints sub (blocksOf sub)).groups[i]? = some gr →
      ∀ n ∈ gr.names, ∀ a ∈ nameRecords ixe n, ∀ c, recordAt ixe a = some c → ∀ r ∈ c.refs,
        ixe.consts.contains r = true →
          ∃ m, addrOf ixe m = some r ∧ (m ∈ gr.names ∨ ∃ j ∈ (graphCollapsed ρ hints sub (blocksOf sub)).hard[i]!,
            ∃ gr' : Group, (graphCollapsed ρ hints sub (blocksOf sub)).groups[j]? = some gr' ∧ m ∈ gr'.names) := by
  intro i gr hgr n hn a ha c hc r hr hcont
  obtain ⟨n', hn', m, hm, href, hout⟩ := compiled i gr hgr n hn a ha c hc r hr hcont
  obtain ⟨c0, hmem⟩ := Ix.LeanIngress.scheduleOf_complete _ (Array.getElem?_eq_some_iff.mp hgr).1
  obtain ⟨q, hq, hqe⟩ := Array.getElem_of_mem hmem
  have hx : ((i, c0), q) ∈ (scheduleOf (graphCollapsed ρ hints sub (blocksOf sub))).zipIdx.toList :=
    Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (by simp [hq, hqe]))
  obtain ⟨conv, hconv⟩ := scheduled _ hx
  obtain ⟨k, hk, hwhere⟩ := GroupRefs.refs_in_hard (x := (i, c0)) hmem hconv hgr hn' href hout
  exact ⟨k, (addrOf_congr hk).trans hm, hwhere⟩

/--
info: 'Ix.Cert.LayoutRefs.layoutRefs_of_compiled' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms layoutRefs_of_compiled

end Ix.Cert.LayoutRefs
