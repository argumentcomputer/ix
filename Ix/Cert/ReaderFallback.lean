import Ix.Cert.ReaderClosureKeys
import Ix.CompileCert.Loop
import IxC.Kernel.Ixon.PreludeShape

/-! # The committed fallback's cache facts

Successful `preludeFor` supplies the checked recursor shape. Fixed address
uniqueness and structural decoder transport supply coherence, without reducing
the long evidence bodies. Coverage of all emitting input references, paired
traces and the `StoredCanonical` connection remain separate obligations.
-/

namespace Ix.Cert.ReaderFallback

open Ix.Kernel Ix.Kernel.Reader Ix.CompileCert

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem fixed_addresses :
    ((RoleData.prelude ++ RoleData.evidence).toList.filterMap (addressOfHex ∘ Prod.fst)).Nodup := by
  decide +kernel

private theorem rel_imp {R S : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (f : ∀ x y, R x y → S x y) : List.Forall₂ S xs ys := by
  induction h with
  | nil => exact .nil
  | cons head _ ih => exact .cons (f _ _ head) ih

private theorem keys_eq {raw : List (String × String)} {out : List (Address × Ixon.Constant)}
    (h : List.Forall₂ (fun r p => addressOfHex r.1 = some p.1) raw out) :
    out.map Prod.fst = raw.filterMap (addressOfHex ∘ Prod.fst) := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [Function.comp_def, head, ih]

theorem decoded_keys (what : String) (raw : Array (String × String))
    {out : Array (Address × Ixon.Constant)} (h : decodeCommitted what raw = .ok out) :
    out.toList.map Prod.fst = raw.toList.filterMap (addressOfHex ∘ Prod.fst) := by
  unfold decodeCommitted at h
  rw [Array.mapM_eq_mapM_toList] at h
  simp only [Functor.map, Except.map] at h
  split at h
  · cases h
  · rename_i ys hr
    cases h
    apply keys_eq
    apply rel_imp (Loop.mapM_forall₂ _ hr)
    intro x p step
    cases ha : addressOfHex x.1 with
    | none => simp [ha] at step
    | some a =>
      cases hb : bytesOfHex x.2 with
      | none => simp [ha, hb] at step
      | some bytes =>
        simp only [ha, hb] at step
        obtain ⟨_, _, done⟩ := Loop.except_bind_ok.mp step
        cases done
        rfl

theorem preludeFor_records {md : Mode} {t : RoleTable} {pre : Prelude md}
    (h : preludeFor t = .ok pre) :
    preludeRecords = .ok pre.records ∧ evidenceRecords = .ok pre.evidence := by
  have read := (preludeFor_checks h).1
  unfold preludeRead at read
  obtain ⟨rs, hr, read⟩ := Loop.except_bind_ok.mp read
  obtain ⟨es, he, read⟩ := Loop.except_bind_ok.mp read
  obtain ⟨_, _, read⟩ := Loop.except_bind_ok.mp read
  unfold readPrelude at read
  dsimp only at read
  split at read <;> cases read
  exact ⟨hr, he⟩

theorem preludeFor_keys {md : Mode} {t : RoleTable} {pre : Prelude md}
    (h : preludeFor t = .ok pre) : ((pre.records ++ pre.evidence).toList.map Prod.fst).Nodup := by
  obtain ⟨hr, he⟩ := preludeFor_records h
  rw [Array.toList_append, List.map_append, decoded_keys "prelude" _ hr, decoded_keys "evidence" _ he]
  simpa only [Array.toList_append, List.filterMap_append] using fixed_addresses

theorem preludeFor_singletons {md : Mode} {t : RoleTable} {pre : Prelude md}
    (h : preludeFor t = .ok pre) : ∀ a c, (a, c) ∈ pre.records ++ pre.evidence →
      ∀ position recursor, (position, recursor) ∈ recursorMembers c → ∃ value, c.info = .recr value := by
  have checked := (preludeFor_checks h).2.2
  unfold checkFallbackRecursors at checked
  split at checked
  · rename_i all
    intro a c present position recursor member
    have good := Array.all_eq_true_iff_forall_mem.mp all (a, c) present
    have source := ReaderIndex.member_source c position recursor member
    cases kind : c.info with
    | recr value => exact ⟨value, rfl⟩
    | muts ms =>
      simp only [fallbackRecursorShape, kind] at good
      rw [kind] at source
      have impossible := Array.all_eq_true_iff_forall_mem.mp good (.recr recursor) (Array.mem_of_getElem? source)
      cases impossible
    | _ => simp only [kind] at source
  · cases checked

section Context

variable {md : Mode} (t : RoleTable) (pre : Prelude md) (input : Array (Address × Ixon.Constant))
    (blobs : List (Address × ByteArray)) (hint : ConstRef Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef Address → Option Address)

local notation "cx" => (contextOf (md := md) t input blobs (pre.records ++ pre.evidence) pre.blobs hint reconstruct)

theorem context_coherent (prepared : preludeFor t = .ok pre)
    (unique : (input.toList.map Prod.fst).Nodup) :
    ReaderIndex.Coherent (cx).store (ReaderClosureKeys.scanned input (pre.records ++ pre.evidence)) :=
  ReaderClosureKeys.context_coherent_of_nodup t input _ blobs pre.blobs hint reconstruct unique
    (preludeFor_keys prepared)

/-- The committed fallback discharges the internal premises; mutual input
recursors still need source-row coverage. No arbitrary injected-prelude claim. -/
theorem selected (prepared : preludeFor t = .ok pre) (unique : (input.toList.map Prod.fst).Nodup)
    {block : Address} {shape : BlockShape} {ref : ConstRef Address}
    (found : (cx).index.blocks[block]? = some shape) (chosen : ref ∈ shape.recs) :
    (∃ b, (cx).keys.address[ref]? = some b) ∨
      ∃ owner c position recursor members, (owner, c) ∈ input ∧ ref = .member owner position ∧
        c.info = .muts members ∧ members[position]? = some (.recr recursor) := by
  apply ReaderClosureKeys.selected_cached_or_input_mutual t input _ blobs pre.blobs hint reconstruct unique
    ?_ (preludeFor_singletons prepared) found chosen
  intro a c present
  rw [ReaderClosureKeys.recordMap_get]
  exact ReaderClosureKeys.lookup_of_nodup (preludeFor_keys prepared) (Array.mem_toList_iff.mpr present)

end Context
end Ix.Cert.ReaderFallback
