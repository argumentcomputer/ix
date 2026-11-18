import IxVMRefinement.Claim.RoleTable
import IxVMRefinement.Roles.Lookups

/-! # The role table as `KernelRoles::load_role_table` parses it

`Claim.load_role_table_spec` reads the load against a table given in advance. Here the table is
produced by the load itself: the readers `read_role_bindings`, `read_role_evidence` and
`read_evidence_entries` are read in the parse direction, from the bytes of the stream to the
pairs they hold, and the maps the load builds are described exactly (every parsed pair is an
entry and every entry is a parsed pair), not only soundly as `Core.TableRep` describes them.

* `RoleMapEntries en h es tree`: the in-order entries of a role-keyed map
  (`KernelRoles::RoleMap<V>`); with ascending keys a search finds every entry
  (`RoleMapEntries.search_of_mem`).
* `rbtreeEntries_det`: an address-keyed map's entries are determined by the tree.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.RoleVal

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Role-keyed maps, exactly -/

/-- **The in-order entries of a role-keyed map** (`KernelRoles::RoleMap<V>`, held by value:
`Node(color, key, value, &left, &right)`), keys as natural numbers. -/
inductive RoleMapEntries (en : String) (h : Heap F) :
    List (Nat × SourceValue F) → SourceValue F → Prop where
  | nil : RoleMapEntries en h [] (.construct en "Nil" [])
  | node {c : F} {k : Nat} {v lp rp lv rv : SourceValue F}
      {ls rs : List (Nat × SourceValue F)}
      (hl : loadValue h lp = .ok lv) (hr : loadValue h rp = .ok rv)
      (rl : RoleMapEntries en h ls lv) (rr : RoleMapEntries en h rs rv) :
      RoleMapEntries en h (ls ++ [(k, v)] ++ rs)
        (.construct en "Node" [.field c, .field (k : F), v, lp, rp])

theorem RoleMapEntries.mono {en : String} {h₁ h₂ : Heap F}
    {es : List (Nat × SourceValue F)} {tree : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (he : RoleMapEntries en h₁ es tree) :
    RoleMapEntries en h₂ es tree := by
  induction he with
  | nil => exact .nil
  | node hl hr _ _ ihl ihr => exact .node (ext.loadValue_eq hl) (ext.loadValue_eq hr) ihl ihr

/-- Every entry of a map with these entries satisfies what each entry satisfies. -/
theorem RoleMapEntries.toAll {en : String} {h : Heap F} {es : List (Nat × SourceValue F)}
    {tree : SourceValue F} {P : Heap F → F → SourceValue F → Prop}
    (he : RoleMapEntries en h es tree) (hP : ∀ p ∈ es, P h (p.1 : F) p.2) :
    RoleMapAll en P h tree := by
  induction he with
  | nil => exact .nil
  | @node c k v lp rp lv rv ls rs hl hr _ _ ihl ihr =>
    exact .node (hP (k, v) (by simp)) hl hr
      (ihl (fun p hp => hP p (by simp [hp])))
      (ihr (fun p hp => hP p (by simp [hp])))

/-- **A search for a key of an ascending role map finds its entry.** -/
theorem RoleMapEntries.search_of_mem {en : String} {h : Heap F}
    {es : List (Nat × SourceValue F)} {tree : SourceValue F}
    (he : RoleMapEntries en h es tree) :
    es.Pairwise (fun p q => p.1 < q.1) → (∀ p ∈ es, p.1 < 4294967296) →
    ∀ {k : Nat} {v : SourceValue F} {res : Option (SourceValue F)},
      (k, v) ∈ es → Specs.Roles.RoleMapSearch en h (k : F) tree res → res = some v := by
  induction he with
  | nil => intro _ _ k v res hm; cases hm
  | @node c key v0 lp rp lv rv ls rs hl hr rl rr ihl ihr =>
    intro hasc hlt k v res hm hs
    have hk : k < 4294967296 := hlt (k, v) hm
    have hkey : key < 4294967296 := hlt (key, v0) (by simp)
    rw [List.pairwise_append, List.pairwise_append] at hasc
    obtain ⟨⟨hpl, -, hl_mid⟩, hpr, hlr⟩ := hasc
    have hls_lt : ∀ p ∈ ls, p.1 < key := fun p hp => hl_mid p hp (key, v0) (by simp)
    have hrs_gt : ∀ p ∈ rs, key < p.1 := fun p hp => hlr (key, v0) (by simp) p hp
    have hltL : ∀ p ∈ ls, p.1 < 4294967296 := fun p hp => hlt p (by simp [hp])
    have hltR : ∀ p ∈ rs, p.1 < 4294967296 := fun p hp => hlt p (by simp [hp])
    simp only [List.append_assoc, List.singleton_append, List.mem_append, List.mem_cons,
      Prod.mk.injEq] at hm
    generalize hT : (Value.construct en "Node" [.field c, .field (key : F), v0, lp, rp] :
      SourceValue F) = T at hs
    cases hs with
    | nil =>
      injection hT with _ hc _
      exact absurd hc (by decide)
    | @here c' v' lp' rp' =>
      injection hT with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hkk, rfl, -, -⟩ := hargs
      have hke : key = k := Claim.natCast_inj_of_lt_u32 hkey hk (Value.field.inj hkk)
      subst hke
      rcases hm with hm | ⟨-, rfl⟩ | hm
      · exact absurd (hls_lt _ hm) (Nat.lt_irrefl _)
      · rfl
      · exact absurd (hrs_gt _ hm) (Nat.lt_irrefl _)
    | @left c' v' lp' rp' lv' key' res' hlt' hl' hs' =>
      injection hT with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hkk, -, rfl, -⟩ := hargs
      obtain rfl := Claim.loadValue_eq_inj hl hl'
      rw [← Value.field.inj hkk, Claim.val_of_lt_u32 hk, Claim.val_of_lt_u32 hkey] at hlt'
      rcases hm with hm | hm | hm
      · exact ihl hpl hltL hm hs'
      · exact absurd hm.1 (Nat.ne_of_lt hlt')
      · exact absurd (Nat.lt_trans hlt' (hrs_gt _ hm)) (Nat.lt_irrefl _)
    | @right c' v' lp' rp' rv' key' res' hgt' hr' hs' =>
      injection hT with _ _ hargs
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, hkk, -, -, rfl⟩ := hargs
      obtain rfl := Claim.loadValue_eq_inj hr hr'
      rw [← Value.field.inj hkk, Claim.val_of_lt_u32 hk, Claim.val_of_lt_u32 hkey] at hgt'
      rcases hm with hm | hm | hm
      · exact absurd (Nat.lt_trans hgt' (hls_lt _ hm)) (Nat.lt_irrefl _)
      · exact absurd hm.1 (Nat.ne_of_gt hgt')
      · exact ihr hpr hltR hm hs'

/-! ## Address-keyed maps: entries determined by the tree -/

/-- **The entries of an address-keyed map are determined by the tree and the heap.** -/
theorem rbtreeEntries_det {t_V : Generic.Ty} {h : Heap F}
    {es : List (Bytes.Address × SourceValue F)} {tree : SourceValue F}
    (he : Claim.RBTreeEntries t_V h es tree) :
    ∀ {es' : List (Bytes.Address × SourceValue F)}, Claim.RBTreeEntries t_V h es' tree →
      es = es' := by
  induction he with
  | nil => intro es' h'; exact h'.nil_inv.symm
  | node hk hl hr rl rr ihl ihr =>
    intro es' h'
    obtain ⟨c', a', lv', rv', ls', rs', -, rfl, hk', hl', hr', rl', rr'⟩ := h'.node_inv
    obtain rfl := Claim.loadValue_eq_inj hl hl'
    obtain rfl := Claim.loadValue_eq_inj hr hr'
    obtain rfl := Bytes.repAddressRef_inj Aiur.Library.U32.Goldilocks.compatible hk hk'
    rw [ihl rl', ihr rr']

end IxVM.Refinement.RoleVal
