import Ix.Cert.FallbackStore
import Ix.Cert.LowerDistinct
import Ix.Cert.LowerTransfer
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.ReaderFallback
import Ix.Cert.ReadingKeys
import Ix.Cert.Stream
import Ix.CompileCert.InductiveReading
import Ix.CompileCert.ReaderIndex
import Ix.IxVM.Consistency.Statement
import IxVMRefinement.L1.Decode
import IxVMRefinement.RoleVal.CommittedData
import IxVMRefinement.RoleVal.ReaderTableDecide

/-! # `ReaderTable` (`defaultBinding` & `TableAdmitted`) and fallback collision agreement

Given `IxVM.Consistency.ReaderTable clm V b` and
`Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t`, establishes:
* `preludeFor_defaultRoleTable` and `preludeFor_of_readerTable`:
  `∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) t = .ok pre`;
* `literalSupportBound_of_readerTable`: `IxVM.Refinement.LiteralSupportBound t`;
* `committedImages_agree_of_loadedBy`, `fallback_record_agree_of_loadedBy`,
  `fallback_recordAt_of_loadedBy`, and `fallback_blob_agree_of_loadedBy`:
  either `V.HashedCollision extra calls` holds (for any `extra` containing `committedImages`,
  in particular `bytes :: b.bytes :: committedImages`), or every record and blob in `pre`'s
  fallback (`pre.records`, `pre.evidence`, `pre.blobs`) agrees byte-for-byte with any `E₀`
  satisfying `IxVM.Consistency.LoadedBy calls E₀`. -/

namespace IxVM.Refinement.RoleVal

open Aiur.Generic.SourceSemantics (Call)
open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Store, role-binding, and recursor-index agreement on `committedDefaultRoleTable` -/

private theorem lookup_isSome_of_mem_map_fst {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} (h : k ∈ l.map Prod.fst) :
    (l.lookup k).isSome = true := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    rw [List.lookup_cons]
    by_cases heq : k == hd.1
    · simp [heq]
    · simp only [heq]
      rcases List.mem_cons.mp h with rfl | htl
      · simp at heq
      · exact ih htl

private theorem lookup_eq_none_of_not_mem_map_fst {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} (h : k ∉ l.map Prod.fst) :
    l.lookup k = none := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.lookup_cons]
    have hne : (k == hd.1) = false :=
      Bool.eq_false_iff.mpr fun hc => h (by rw [beq_iff_eq.mp hc]; exact List.mem_cons_self)
    rw [hne]
    exact ih fun hm => h (List.mem_cons_of_mem _ hm)

private theorem mem_of_lookup_eq_some {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} {v : β} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    rw [List.lookup_cons] at h
    by_cases heq : k == hd.1
    · rw [heq] at h
      injection h with hv
      subst hv
      rcases hd with ⟨k', v⟩
      dsimp only at heq
      rw [beq_iff_eq.mp heq]
      exact List.mem_cons_self
    · rw [Bool.eq_false_iff.mpr heq] at h
      exact List.mem_cons_of_mem _ (ih h)

private theorem pre_refs_mem {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ committedPreludeList) {r : _root_.Address} (hr : r ∈ c.refs.toList) :
    r ∈ committedPreAddrs := by
  have hall := List.all_eq_true.mp preRefsAndProjClosed (a, c) hc
  rw [Bool.and_eq_true, List.all_eq_true] at hall
  have hr' := hall.1 r hr
  rw [containsAddrFast_eq, List.contains_iff_mem] at hr'
  exact hr'

private theorem pre_proj_block_mem {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ committedPreludeList) :
    (∀ p, c.info = .cPrj p → p.block ∈ committedPreAddrs) ∧
    (∀ p, c.info = .rPrj p → p.block ∈ committedPreAddrs) ∧
    (∀ p, c.info = .iPrj p → p.block ∈ committedPreAddrs) ∧
    (∀ p, c.info = .dPrj p → p.block ∈ committedPreAddrs) := by
  have hall0 := List.all_eq_true.mp preRefsAndProjClosed (a, c) hc
  rw [Bool.and_eq_true] at hall0
  have hall := hall0.2
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (intro p hp; rw [hp] at hall; dsimp only at hall;
     rw [containsAddrFast_eq, List.contains_iff_mem] at hall; exact hall)

private theorem contextOf_store (t : Ix.Kernel.RoleTable)
    (records : Array (_root_.Address × Ixon.Constant))
    (blobs : List (_root_.Address × ByteArray))
    (fallback : Array (_root_.Address × Ixon.Constant))
    (fallbackBlobs : List (_root_.Address × ByteArray)) (a : _root_.Address) :
    (contextOf (md := .anon) t records blobs fallback fallbackBlobs).store a =
      ((recordMap records)[a]? <|> ((recordMap fallback)[a]? <|> none)) :=
  rfl

private theorem contextOf_roles (t : Ix.Kernel.RoleTable)
    (records : Array (_root_.Address × Ixon.Constant))
    (blobs : List (_root_.Address × ByteArray))
    (fallback : Array (_root_.Address × Ixon.Constant))
    (fallbackBlobs : List (_root_.Address × ByteArray)) :
    (contextOf (md := .anon) t records blobs fallback fallbackBlobs).roles =
      bindingsOf (contextOf (md := .anon) t records blobs fallback fallbackBlobs).store t :=
  rfl

private theorem contextOf_index (t : Ix.Kernel.RoleTable)
    (records : Array (_root_.Address × Ixon.Constant))
    (blobs : List (_root_.Address × ByteArray))
    (fallback : Array (_root_.Address × Ixon.Constant))
    (fallbackBlobs : List (_root_.Address × ByteArray)) :
    (contextOf (md := .anon) t records blobs fallback fallbackBlobs).index =
      buildIndex (contextOf (md := .anon) t records blobs fallback fallbackBlobs).store
        (indexedRecords (contextOf (md := .anon) t records blobs fallback fallbackBlobs).store
          records fallback) :=
  rfl

private theorem option_bind_eq_some {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

private theorem ite_not_eq_some {α : Type} {b : Bool} {t : Option α} {y : α}
    (h : (if (!b) = true then none else t) = some y) :
    b = true ∧ t = some y := by
  cases b
  · cases h
  · exact ⟨rfl, h⟩

private theorem option_guard_true {b : Bool} (hb : b = true) :
    (guard (b = true) : Option Unit) = some () := by
  subst hb; rfl

private theorem id_pure {α : Type} (x : α) :
    (pure x : Id α) = x :=
  rfl

private theorem option_some_bind {α β : Type} (a : α) (f : α → Option β) :
    (some a >>= f) = f a :=
  rfl

private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a :=
  rfl

private theorem readPrelude_eq (t : Ix.Kernel.RoleTable)
    (records extra : Array (_root_.Address × Ixon.Constant))
    (extraBlobs : List (_root_.Address × ByteArray)) :
    readPrelude (md := .anon) t records extra extraBlobs =
      match readRecords (contextOf t records [] extra extraBlobs) {} records with
      | .ok (state, decls) =>
        Except.ok ⟨records, extra, extraBlobs, ⟨decls⟩, state⟩
      | .error (e, i) =>
        throw s!"prelude record {i}: {e}" := by
  unfold readPrelude
  dsimp only
  cases readRecords (contextOf t records [] extra extraBlobs) {} records with
  | ok p => rcases p with ⟨_, _⟩; rfl
  | error e => rcases e with ⟨_, _⟩; rfl

section WithEv

variable (ev : Array (_root_.Address × Ixon.Constant))
  (hev_defn : ∀ p ∈ ev.toList, ∃ d, p.2.info = .defn d)

private def defCx : Ctx .anon :=
  contextOf committedDefaultRoleTable committedPrelude [] ev committedBlobs

private theorem defCx_store_eq (a : _root_.Address) :
    (defCx ev).store a = ((recordMap committedPrelude)[a]? <|> ((recordMap ev)[a]? <|> none)) := by
  unfold defCx
  exact contextOf_store committedDefaultRoleTable committedPrelude [] ev committedBlobs a

private theorem defCx_roles_eq :
    (defCx ev).roles = bindingsOf (defCx ev).store committedDefaultRoleTable := by
  unfold defCx
  exact contextOf_roles committedDefaultRoleTable committedPrelude [] ev committedBlobs

private theorem defCx_index_eq :
    (defCx ev).index =
      buildIndex (defCx ev).store (indexedRecords (defCx ev).store committedPrelude ev) := by
  unfold defCx
  exact contextOf_index committedDefaultRoleTable committedPrelude [] ev committedBlobs

private theorem readPrelude_defCx_eq :
    readPrelude (md := .anon) committedDefaultRoleTable committedPrelude ev committedBlobs =
      match readRecords (defCx ev) {} committedPrelude with
      | .ok (state, decls) =>
        Except.ok ⟨committedPrelude, ev, committedBlobs, ⟨decls⟩, state⟩
      | .error (e, i) =>
        throw s!"prelude record {i}: {e}" := by
  unfold defCx
  exact readPrelude_eq committedDefaultRoleTable committedPrelude ev committedBlobs

attribute [irreducible] defCx

private theorem defCx_store_of_mem_pre {a : _root_.Address} (ha : a ∈ committedPreAddrs) :
    (defCx ev).store a = preStorePure a := by
  rw [preStorePure_eq, defCx_store_eq ev]
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get, show committedPrelude.toList = committedPreludeList from rfl]
  have hs := lookup_isSome_of_mem_map_fst ha
  cases hl : committedPreludeList.lookup a with
  | none => rw [hl] at hs; cases hs
  | some _ => rfl

private theorem resolveSource_defCx_eq_pure {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ committedPreludeList) :
    resolveSource (defCx ev).store a c = resolveSource preStorePure a c := by
  have hblk := pre_proj_block_mem hc
  unfold resolveSource
  cases hci : c.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => rfl
  | cPrj p => dsimp only; rw [defCx_store_of_mem_pre ev (hblk.1 p hci)]
  | rPrj p => dsimp only; rw [defCx_store_of_mem_pre ev (hblk.2.1 p hci)]
  | iPrj p => dsimp only; rw [defCx_store_of_mem_pre ev (hblk.2.2.1 p hci)]
  | dPrj p => dsimp only; rw [defCx_store_of_mem_pre ev (hblk.2.2.2 p hci)]

private theorem resolve_defCx_of_mem_pre {a : _root_.Address} (ha : a ∈ committedPreAddrs) :
    resolve (defCx ev).store a = resolve preStorePure a := by
  unfold resolve
  rw [defCx_store_of_mem_pre ev ha, preStorePure_eq]
  cases hl : committedPreludeList.lookup a with
  | none => rfl
  | some c =>
    simp only [bind, Option.bind]
    exact resolveSource_defCx_eq_pure ev (mem_of_lookup_eq_some hl)

include hev_defn in
private theorem resolve_defCx_not_mem_pre {a : _root_.Address}
    (ha : a ∉ committedPreAddrs) {ref : ConstRef _root_.Address}
    (hres : resolve (defCx ev).store a = some ref) :
    constRefBlock ref ∉ committedPreAddrs := by
  unfold resolve at hres
  have hpre_none : (recordMap committedPrelude)[a]? = none := by
    rw [Ix.Cert.ReaderClosureKeys.recordMap_get, show committedPrelude.toList = committedPreludeList from rfl]
    exact lookup_eq_none_of_not_mem_map_fst ha
  have hst : (defCx ev).store a = ev.toList.lookup a := by
    rw [defCx_store_eq ev, hpre_none, Ix.Cert.ReaderClosureKeys.recordMap_get]
    cases ev.toList.lookup a <;> rfl
  rw [hst] at hres
  cases hel : ev.toList.lookup a with
  | none => rw [hel] at hres; cases hres
  | some c =>
    rw [hel] at hres
    obtain ⟨d, hd⟩ := hev_defn (a, c) (mem_of_lookup_eq_some hel)
    dsimp only at hd
    simp only [bind, Option.bind, resolveSource, hd, Option.some.injEq] at hres
    rw [← hres]
    exact ha

/-! ### Role bindings agreement -/

private def bindingsStep (store : Store)
    (m : Std.HashMap (ConstRef _root_.Address) (CName .anon))
    (p : Ix.Kernel.Role × _root_.Address) :
    Std.HashMap (ConstRef _root_.Address) (CName .anon) :=
  match resolve store p.2 with
  | some ref => if m.contains ref then m else m.insert ref (Ix.Kernel.roleKey p.1)
  | none => m

private theorem bindingsStep_preserves (store : Store)
    (m : Std.HashMap (ConstRef _root_.Address) (CName .anon))
    (p : Ix.Kernel.Role × _root_.Address) {ref₀ : ConstRef _root_.Address} {k₀ : CName .anon}
    (hm : m[ref₀]? = some k₀) :
    (bindingsStep store m p)[ref₀]? = some k₀ := by
  unfold bindingsStep
  cases hrs : resolve store p.2 with
  | none => exact hm
  | some ref =>
    dsimp only
    by_cases hc : m.contains ref = true
    · simp only [hc, ↓reduceIte]; exact hm
    · simp only [Bool.not_eq_true _ |>.mp hc, Bool.false_eq_true, ↓reduceIte]
      have hne : ref ≠ ref₀ := by
        rintro rfl
        rw [Std.HashMap.contains_eq_isSome_getElem?, hm] at hc
        exact hc rfl
      rw [Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.mpr hne]
      exact hm

private theorem foldl_bindingsStep_preserves (store : Store)
    {ref₀ : ConstRef _root_.Address} {k₀ : CName .anon} :
    ∀ (l : List (Ix.Kernel.Role × _root_.Address))
      (m : Std.HashMap (ConstRef _root_.Address) (CName .anon)),
      m[ref₀]? = some k₀ →
      (l.foldl (bindingsStep store) m)[ref₀]? = some k₀
  | [], m, hm => hm
  | p :: l, m, hm =>
    foldl_bindingsStep_preserves store l (bindingsStep store m p)
      (bindingsStep_preserves store m p hm)

include hev_defn in
private theorem foldl_bindingsStep_lookup
    {ref₀ : ConstRef _root_.Address} {k₀ : CName .anon}
    (hblk : constRefBlock ref₀ ∈ committedPreAddrs) :
    ∀ (l : List (Ix.Kernel.Role × _root_.Address))
      (m : Std.HashMap (ConstRef _root_.Address) (CName .anon)),
      m[ref₀]? = none →
      (l.filterMap fun (ro, a) =>
        if committedPreAddrs.contains a then
          (resolve preStorePure a).map fun ref => (ref, Ix.Kernel.roleKey (md := .anon) ro)
        else none).lookup ref₀ = some k₀ →
      (l.foldl (bindingsStep (defCx ev).store) m)[ref₀]? = some k₀
  | [], _, _, hlk => by cases hlk
  | (ro, a) :: l, m, hnone, hlk => by
    rw [List.foldl_cons]
    by_cases hpa : committedPreAddrs.contains a = true
    · have ha_mem : a ∈ committedPreAddrs := List.contains_iff_mem.mp hpa
      simp only [List.filterMap_cons, hpa, ↓reduceIte] at hlk
      cases hrp : resolve preStorePure a with
      | none =>
        simp only [hrp, Option.map_none] at hlk
        have hstep : bindingsStep (defCx ev).store m (ro, a) = m := by
          unfold bindingsStep; dsimp only
          rw [resolve_defCx_of_mem_pre ev ha_mem, hrp]
        rw [hstep]
        exact foldl_bindingsStep_lookup hblk l m hnone hlk
      | some ref =>
        simp only [hrp, Option.map_some, List.lookup_cons] at hlk
        by_cases heq : ref₀ == ref
        · rw [heq] at hlk
          injection hlk with hk
          subst hk
          have href_eq : ref = ref₀ := (beq_iff_eq.mp heq).symm
          subst ref
          have hstep : (bindingsStep (defCx ev).store m (ro, a))[ref₀]? = some (Ix.Kernel.roleKey ro) := by
            unfold bindingsStep; dsimp only
            rw [resolve_defCx_of_mem_pre ev ha_mem, hrp]; dsimp only
            rw [Std.HashMap.contains_eq_isSome_getElem?, hnone]
            simp [Std.HashMap.getElem?_insert]
          exact foldl_bindingsStep_preserves (defCx ev).store l _ hstep
        · rw [Bool.not_eq_true _ |>.mp heq] at hlk
          have hstep_none : (bindingsStep (defCx ev).store m (ro, a))[ref₀]? = none := by
            unfold bindingsStep; dsimp only
            rw [resolve_defCx_of_mem_pre ev ha_mem, hrp]; dsimp only
            split
            · exact hnone
            · have hne : (ref == ref₀) = false :=
                beq_eq_false_iff_ne.mpr fun h => heq (beq_iff_eq.mpr h.symm)
              rw [Std.HashMap.getElem?_insert, hne]
              exact hnone
          exact foldl_bindingsStep_lookup hblk l _ hstep_none hlk
    · have ha_not : a ∉ committedPreAddrs := fun hm => hpa (List.contains_iff_mem.mpr hm)
      simp only [List.filterMap_cons, Bool.not_eq_true _ |>.mp hpa, Bool.false_eq_true, ↓reduceIte] at hlk
      have hstep_none : (bindingsStep (defCx ev).store m (ro, a))[ref₀]? = none := by
        unfold bindingsStep; dsimp only
        cases hrs : resolve (defCx ev).store a with
        | none => exact hnone
        | some ref =>
          dsimp only
          have hnot_blk := resolve_defCx_not_mem_pre ev hev_defn ha_not hrs
          have hne : ref ≠ ref₀ := fun h => hnot_blk (by rw [h]; exact hblk)
          split
          · exact hnone
          · rw [Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.mpr hne]
            exact hnone
      exact foldl_bindingsStep_lookup hblk l _ hstep_none hlk

include hev_defn in
private theorem defCx_roles_of_pure {ref : ConstRef _root_.Address} {k : CName .anon}
    (h : pureRolesLookup ref = some k) :
    (defCx ev).roles.names[ref]? = some k := by
  unfold pureRolesLookup at h
  rw [lookupConstRefFast_eq] at h
  have hblk : constRefBlock ref ∈ committedPreAddrs :=
    pureRolesList_block_mem (ref, k) (mem_of_lookup_eq_some h)
  have hfn : (fun (p : Ix.Kernel.Role × _root_.Address) =>
      if containsAddrFast committedPreAddrs p.2 then
        (resolve preStorePure p.2).map fun ref => (ref, Ix.Kernel.roleKey (md := .anon) p.1)
      else none) =
    (fun (p : Ix.Kernel.Role × _root_.Address) =>
      if committedPreAddrs.contains p.2 then
        (resolve preStorePure p.2).map fun ref => (ref, Ix.Kernel.roleKey (md := .anon) p.1)
      else none) := by
    funext ⟨ro, a⟩
    rw [containsAddrFast_eq]
  unfold pureRolesList at h
  rw [hfn] at h
  rw [defCx_roles_eq ev]
  unfold bindingsOf
  dsimp only
  rw [← Array.foldl_toList]
  refine Eq.trans ?_ (foldl_bindingsStep_lookup ev hev_defn hblk
    committedDefaultRoleTable.bound.toList {} Std.HashMap.getElem?_empty h)
  congr 1

/-! ### Recursor index agreement -/

private theorem recursorMembersFast_eq (c : Ixon.Constant) :
    recursorMembersFast c = (recursorMembers c).toList := by
  unfold recursorMembersFast recursorMembers
  cases c.info with
  | recr _ => rfl
  | muts ms =>
    dsimp only
    rw [Array.toList_filterMap, Array.toList_zipIdx]
    congr 1
  | _ => rfl

private theorem unshareGoFast_eq (c : Ixon.Constant) :
    ∀ (n : Nat) (e : Ixon.Expr), unshareGoFast c.sharing.toList n e = unshare.go c n e
  | 0, _ => rfl
  | _ + 1, .var _ | _ + 1, .sort _ | _ + 1, .ref _ _ | _ + 1, .recur _ _
  | _ + 1, .prj _ _ _ | _ + 1, .str _ | _ + 1, .nat _ | _ + 1, .app _ _
  | _ + 1, .lam _ _ | _ + 1, .all _ _ | _ + 1, .letE _ _ _ _ _ => rfl
  | n + 1, .share i => by
    unfold unshareGoFast unshare.go
    rw [nth?_eq, Array.getElem?_toList]
    cases c.sharing[i.toNat]? with
    | none => rfl
    | some e' => exact unshareGoFast_eq c n e'

private theorem unshareFast_eq (c : Ixon.Constant) (e : Ixon.Expr) :
    unshareFast c e = unshare c e := by
  unfold unshareFast unshare
  rw [Array.length_toList]
  exact unshareGoFast_eq c _ e

private theorem stripAllFast_eq (c : Ixon.Constant) :
    ∀ (n : Nat) (e : Ixon.Expr), stripAllFast c n e = stripAll c n e
  | 0, _ => rfl
  | n + 1, e => by
    unfold stripAllFast stripAll
    rw [unshareFast_eq]
    cases unshare c e with
    | all t b =>
      dsimp only [bind, Option.bind, pure]
      rw [stripAllFast_eq c n b]
      cases stripAll c n b <;> rfl
    | _ => rfl

private theorem stripAllFullChecked_sound (c : Ixon.Constant) :
    ∀ (k m : Nat) (e : Ixon.Expr) {res : List Ixon.Expr × Ixon.Expr},
      k ≤ m → stripAllFullChecked c k e = some res → stripAllFull c m e = res
  | 0, _, _, _, _, h => by cases h
  | k + 1, 0, _, _, hle, _ => absurd hle (Nat.not_succ_le_zero k)
  | k + 1, m + 1, e, _, hle, h => by
    unfold stripAllFullChecked at h
    unfold stripAllFull
    rw [unshareFast_eq] at h
    cases hu : unshare c e with
    | all t b =>
      rw [hu] at h
      dsimp only at h ⊢
      cases hs : stripAllFullChecked c k b with
      | none => rw [hs] at h; cases h
      | some pair =>
        rcases pair with ⟨ts, r⟩
        rw [hs] at h
        injection h with hres; subst hres
        rw [stripAllFullChecked_sound c k m b (Nat.le_of_succ_le_succ hle) hs]
    | _ =>
      rw [hu] at h
      exact Option.some.inj h

private theorem appHeadChecked_sound (c : Ixon.Constant) :
    ∀ (k m : Nat) (e : Ixon.Expr) {res : Ixon.Expr},
      k ≤ m → appHeadChecked c k e = some res → appHead c m e = res
  | 0, _, _, _, _, h => by cases h
  | k + 1, 0, _, _, hle, _ => absurd hle (Nat.not_succ_le_zero k)
  | k + 1, m + 1, e, _, hle, h => by
    unfold appHeadChecked at h
    unfold appHead
    rw [unshareFast_eq] at h
    cases hu : unshare c e with
    | app f a =>
      rw [hu] at h
      dsimp only at h ⊢
      exact appHeadChecked_sound c k m f (Nat.le_of_succ_le_succ hle) h
    | _ =>
      rw [hu] at h
      exact Option.some.inj h

private theorem headRefChecked_sound (store : Store) (owner : _root_.Address)
    (c : Ixon.Constant) (e : Ixon.Expr) {cr : ConstRef _root_.Address}
    (h : headRefChecked store owner c e = some cr) :
    headRef store owner c e = some cr := by
  unfold headRefChecked at h
  cases hah : appHeadChecked c 64 e with
  | none => rw [hah] at h; cases h
  | some hd =>
    rw [hah] at h
    dsimp only [bind, Option.bind] at h
    have hah' := appHeadChecked_sound c 64 spineFuel e (by decide) hah
    unfold headRef
    rw [hah']
    cases hd with
    | ref i us =>
      dsimp only at h ⊢
      rw [nth?_eq, Array.getElem?_toList] at h
      exact h
    | recur i us =>
      dsimp only at h ⊢
      cases hci : c.info with
      | muts ms => rw [hci] at h; dsimp only at h ⊢; rw [Array.length_toList] at h; exact h
      | _ => rw [hci] at h; dsimp only at h ⊢; exact h
    | _ => cases h

private theorem mapM_option_imp {α β : Type} {f g : α → Option β}
    (hfg : ∀ x y, f x = some y → g x = some y) :
    ∀ (l : List α) {ys : List β}, l.mapM f = some ys → l.mapM g = some ys
  | [], _, h => h
  | x :: xs, _, h => by
    simp only [List.mapM_cons, bind, Option.bind, pure] at h ⊢
    cases hfx : f x with
    | none => rw [hfx] at h; cases h
    | some y =>
      rw [hfx] at h
      cases hxs : xs.mapM f with
      | none => rw [hxs] at h; cases h
      | some ys' =>
        rw [hxs] at h
        rw [hfg x y hfx, mapM_option_imp hfg xs hxs]
        exact h

private theorem analyseRecursorChecked_sound (store : Store) (owner : _root_.Address)
    (c : Ixon.Constant) (r : Ixon.Recursor)
    {motive : Nat} {carriersL : List (ConstRef _root_.Address)}
    {major : ConstRef _root_.Address}
    (h : analyseRecursorChecked store owner c r = some (motive, carriersL, major)) :
    analyseRecursor store owner c r = some (motive, carriersL.toArray, major) := by
  unfold analyseRecursorChecked at h
  dsimp only at h
  obtain ⟨⟨doms, body⟩, hsa0, h⟩ := option_bind_eq_some h
  rw [stripAllFast_eq] at hsa0
  dsimp only at h
  obtain ⟨bhd, hah, h⟩ := option_bind_eq_some h
  have hah' := appHeadChecked_sound c 64 spineFuel body (by decide) hah
  cases bhd with
  | var k =>
    dsimp only at h
    obtain ⟨hcond, h⟩ := ite_not_eq_some h
    obtain ⟨csL, hcar, h⟩ := option_bind_eq_some h
    obtain ⟨ld, hlast, h⟩ := option_bind_eq_some h
    obtain ⟨maj, hmaj, h⟩ := option_bind_eq_some h
    injection h with htuple
    rcases Prod.mk.inj htuple with ⟨rfl, hcm⟩
    rcases Prod.mk.inj hcm with ⟨rfl, rfl⟩
    have hcar' : ((doms.drop r.params.toNat).take r.motives.toNat).mapM
        (fun dom => do
          let (bs, _) := stripAllFull c spineFuel dom
          headRef store owner c (← bs.getLast?)) = some csL := by
      refine mapM_option_imp (fun dom cr hd => ?_) _ hcar
      obtain ⟨⟨bs, _⟩, hsf, hd⟩ := option_bind_eq_some hd
      dsimp only at hd
      obtain ⟨lb, hlb, hd⟩ := option_bind_eq_some hd
      rw [stripAllFullChecked_sound c 64 spineFuel dom (by decide) hsf]
      dsimp only
      rw [hlb, option_some_bind]
      exact headRefChecked_sound store owner c lb hd
    unfold analyseRecursor
    dsimp only
    rw [hsa0, option_some_bind]
    dsimp only
    rw [hah']
    dsimp only
    rw [option_guard_true hcond, option_some_bind]
    rw [Array.mapM_eq_mapM_toList, List.toList_toArray, hcar']
    simp only [hlast, headRefChecked_sound store owner c ld hmaj,
      Functor.map, Option.map, bind, Option.bind, pure]
  | _ => cases h

private theorem inductivesList_eq (members : Array Ixon.MutConst) :
    (inductivesList members.toList).toArray = Ix.CompileCert.ReaderIndex.inductives members := by
  apply Array.ext'
  rw [inductivesList, Ix.CompileCert.ReaderIndex.inductives, List.toList_toArray,
      Array.toList_filterMap, Array.toList_zipIdx]
  congr 1

private theorem orderForList_eq (carriersL : List (ConstRef _root_.Address))
    (owner : _root_.Address) (count : Nat) :
    (orderForList carriersL owner count).toArray =
      Ix.CompileCert.ReaderIndex.orderFor carriersL.toArray owner count := by
  apply Array.ext'
  rw [orderForList, Ix.CompileCert.ReaderIndex.orderFor, List.toList_toArray,
      Array.toList_filterMap, Array.toList_extract, List.extract_eq_take_drop,
      List.drop_zero, Nat.sub_zero, List.toList_toArray]
  congr 1; funext c; cases c <;> simp [beqAddrFast_eq]

private theorem orderValidList_eq (firstIndex : Nat) (indcsL : List (Nat × Ixon.Inductive))
    (orderL : List Nat) :
    orderValidList firstIndex indcsL orderL =
      Ix.CompileCert.ReaderIndex.orderValid firstIndex indcsL.toArray orderL.toArray := by
  unfold orderValidList Ix.CompileCert.ReaderIndex.orderValid
  have hall : orderL.all (fun index => indcsL.any (·.1 == index)) =
      orderL.toArray.all (fun index => indcsL.toArray.any (·.1 == index)) := by
    rw [← Array.all_toList, List.toList_toArray]
    congr 1; funext index
    rw [← Array.any_toList, List.toList_toArray]
  rw [hall, List.size_toArray, List.size_toArray, nth?_eq,
      List.getElem?_toArray, List.toList_toArray]

private def IdxMatches (bs : Ix.CompileCert.ReaderIndex.BuildState) (s : PureIdx) : Prop :=
  (∀ r, bs.1.recs[r]? = s.recs.lookup r) ∧
  (∀ b, bs.1.blocks[b]? = (s.blocks.lookup b).map fun ord => ⟨ord.toArray, #[]⟩) ∧
  (∀ b, bs.2[b]? = (s.found.lookup b).map List.toArray)

private theorem headRef_defCx_eq_pure {owner : _root_.Address} {c : Ixon.Constant}
    (hrefs : c.refs.toList.all committedPreAddrs.contains = true) (e : Ixon.Expr) :
    headRef (defCx ev).store owner c e = headRef preStorePure owner c e := by
  unfold headRef
  cases appHead c spineFuel e with
  | ref i _ =>
    dsimp only
    cases hget : c.refs[i.toNat]? with
    | none => rfl
    | some a =>
      have hmem : a ∈ c.refs.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)
      have hpa : a ∈ committedPreAddrs :=
        List.contains_iff_mem.mp (List.all_eq_true.mp hrefs a hmem)
      exact resolve_defCx_of_mem_pre ev hpa
  | _ => rfl

private theorem analyseRecursor_defCx_eq_pure {owner : _root_.Address} {c : Ixon.Constant}
    (hrefs : c.refs.toList.all committedPreAddrs.contains = true) (r : Ixon.Recursor) :
    analyseRecursor (defCx ev).store owner c r = analyseRecursor preStorePure owner c r := by
  unfold analyseRecursor
  have hh := headRef_defCx_eq_pure ev (owner := owner) hrefs
  simp only [hh]

private theorem foldl_insert_contains :
    ∀ (l : List (_root_.Address × Ixon.Constant)) (pre : List _root_.Address)
      (s : Std.HashSet _root_.Address),
      (∀ x, s.contains x = true ↔ x ∈ pre) →
      ∀ x, (l.foldl (fun acc (a, _) => acc.insert a) s).contains x = true ↔
        x ∈ pre ∨ x ∈ l.map Prod.fst
  | [], pre, s, hs, x => by simp [hs x]
  | (a, c) :: l, pre, s, hs, x => by
    rw [List.foldl_cons, List.map_cons, List.mem_cons]
    have hs' : ∀ y, (s.insert a).contains y = true ↔ y ∈ a :: pre := by
      intro y
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, hs y, beq_iff_eq, List.mem_cons]
      exact ⟨fun h => h.elim (fun h1 => .inl h1.symm) .inr,
        fun h => h.elim (fun h1 => .inl h1.symm) .inr⟩
    rw [foldl_insert_contains l (a :: pre) (s.insert a) hs' x, List.mem_cons]
    tauto

private theorem filter_committedPrelude_inputIndexed :
    committedPrelude.filter (fun (a, c) =>
      inputIndexed (defCx ev).store
        (committedPrelude.foldl (fun s (a, _) => s.insert a) {}) ev a c) =
    committedPrelude := by
  let known : Std.HashSet _root_.Address :=
    committedPrelude.foldl (fun s (a, _) => s.insert a) {}
  have hknown : ∀ x, known.contains x = true ↔ x ∈ committedPreAddrs := by
    intro x
    show (committedPrelude.foldl (fun s (a, _) => s.insert a) ({} : Std.HashSet _root_.Address)).contains x = true ↔ _
    rw [← Array.foldl_toList, show committedPrelude.toList = committedPreludeList from rfl]
    simpa [committedPreAddrs] using
      foldl_insert_contains committedPreludeList [] ({} : Std.HashSet _root_.Address) (by simp) x
  apply Array.ext'
  rw [Array.toList_filter, List.filter_eq_self]
  intro ⟨a, c⟩ hmem
  dsimp only
  have hmem' : (a, c) ∈ committedPreludeList := hmem
  have hrefs : c.refs.toList.all committedPreAddrs.contains = true := by
    have h0 := List.all_eq_true.mp preRefsAndProjClosed (a, c) hmem'
    rw [Bool.and_eq_true, List.all_eq_true] at h0
    rw [List.all_eq_true]
    intro r hr
    have h2 := h0.1 r hr
    rwa [containsAddrFast_eq] at h2
  have hpure0 := preInputIndexed_true
  unfold preInputIndexedBool at hpure0
  have hpure := List.all_eq_true.mp hpure0 (a, c) hmem'
  dsimp only at hpure
  rw [recursorMembersFast_eq, List.all_eq_true] at hpure
  unfold inputIndexed
  rw [Bool.or_eq_true]
  left
  rw [Array.all_eq_true_iff_forall_mem]
  intro ⟨j, r⟩ hjr
  dsimp only
  have hp := hpure (j, r) (Array.mem_toList_iff.mpr hjr)
  dsimp only at hp
  rw [analyseRecursor_defCx_eq_pure ev (owner := a) hrefs r]
  cases han : analyseRecursorChecked preStorePure a c r with
  | none => rw [han] at hp; cases hp
  | some triple =>
    rcases triple with ⟨m, carriersL, major⟩
    rw [han] at hp
    rw [analyseRecursorChecked_sound preStorePure a c r han]
    cases carriersL with
    | nil => cases hp
    | cons cr tl =>
      cases cr with
      | ctor _ _ _ => cases hp
      | member b idx =>
        dsimp only at hp ⊢
        rw [List.getElem?_toArray]
        rw [containsAddrFast_eq] at hp
        exact (hknown b).mpr (List.contains_iff_mem.mp hp)

private theorem candidate_matches_of_pureCandStep {owner : _root_.Address} {c : Ixon.Constant}
    {m : Nat × Ixon.Recursor} {s s' : PureIdx} {bs : Ix.CompileCert.ReaderIndex.BuildState}
    (hm : IdxMatches bs s) (hp : pureCandStep owner c m s = some s') :
    IdxMatches
      (match Ix.CompileCert.ReaderIndex.candidate (defCx ev).store owner c m bs with
       | .yield b | .done b => b) s' := by
  rcases m with ⟨pos, rec⟩
  rcases bs with ⟨idx, found⟩
  obtain ⟨hrecs, hblocks, hfound⟩ := hm
  unfold pureCandStep at hp
  dsimp only [bind, Option.bind] at hp
  rw [lookupConstRefFast_eq] at hp
  cases hrnone : (s.recs.lookup (.member owner pos)).isNone with
  | false => rw [hrnone] at hp; cases hp
  | true =>
    simp only [hrnone, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
    have hcfn : containsAddrFast committedPreAddrs = committedPreAddrs.contains := by
      funext x; exact containsAddrFast_eq committedPreAddrs x
    rw [hcfn] at hp
    cases hrefs : c.refs.toList.all committedPreAddrs.contains with
    | false => rw [hrefs] at hp; cases hp
    | true =>
      simp only [hrefs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
      cases han_chk : analyseRecursorChecked preStorePure owner c rec with
      | none => rw [han_chk] at hp; cases hp
      | some triple =>
        rcases triple with ⟨motive, carriersL, major⟩
        rw [han_chk] at hp
        dsimp only at hp
        have han := analyseRecursorChecked_sound preStorePure owner c rec han_chk
        rw [nth?_eq] at hp
        cases hc0L : carriersL[0]? with
        | none => rw [hc0L] at hp; cases hp
        | some cr0 =>
          rw [hc0L] at hp
          cases cr0 with
          | ctor _ _ _ => cases hp
          | member block firstIdx =>
            dsimp only at hp
            have hc0 : (carriersL.toArray)[0]? = some (.member block firstIdx) := by
              rw [List.getElem?_toArray]; exact hc0L
            cases hblk : committedPreAddrs.contains block with
            | false => rw [hblk] at hp; cases hp
            | true =>
              simp only [hblk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
              cases hbrec : preStorePure block with
              | none => rw [hbrec] at hp; cases hp
              | some blockRec =>
                rw [hbrec] at hp
                dsimp only at hp
                cases hbi : blockRec.info with
                | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
                  rw [hbi] at hp; cases hp
                | muts members =>
                  rw [hbi] at hp
                  dsimp only at hp
                  rw [nth?_eq] at hp
                  cases hind0L : (inductivesList members.toList)[0]? with
                  | none => rw [hind0L] at hp; cases hp
                  | some ifirst =>
                    rcases ifirst with ⟨slot, first⟩
                    rw [hind0L] at hp
                    dsimp only at hp
                    have hind0 : (Ix.CompileCert.ReaderIndex.inductives members)[0]? = some (slot, first) := by
                      rw [← inductivesList_eq, List.getElem?_toArray]; exact hind0L
                    have hsz_ind : (inductivesList members.toList).length =
                        (Ix.CompileCert.ReaderIndex.inductives members).size := by
                      rw [← inductivesList_eq, List.size_toArray]
                    rw [orderValidList_eq, inductivesList_eq, hsz_ind, orderForList_eq] at hp
                    cases hord : Ix.CompileCert.ReaderIndex.orderValid firstIdx
                        (Ix.CompileCert.ReaderIndex.inductives members)
                        (Ix.CompileCert.ReaderIndex.orderFor carriersL.toArray block
                          (Ix.CompileCert.ReaderIndex.inductives members).size) with
                    | false => rw [hord] at hp; cases hp
                    | true =>
                      simp only [hord, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                        lookupAddrFast_eq] at hp
                      cases hfnone : (s.found.lookup block).isNone with
                      | false => rw [hfnone] at hp; cases hp
                      | true =>
                        simp only [hfnone, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
                        cases hbnone : (s.blocks.lookup block).isNone with
                        | false => rw [hbnone] at hp; cases hp
                        | true =>
                          simp only [hbnone, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                            Option.some.injEq] at hp
                          subst hp
                          have hr_lk : s.recs.lookup (.member owner pos) = none :=
                            Option.isNone_iff_eq_none.mp hrnone
                          have hf_lk : s.found.lookup block = none :=
                            Option.isNone_iff_eq_none.mp hfnone
                          have hb_lk : s.blocks.lookup block = none :=
                            Option.isNone_iff_eq_none.mp hbnone
                          have hr_cont : idx.recs.contains (.member owner pos) = false := by
                            rw [Std.HashMap.contains_eq_isSome_getElem?, hrecs, hr_lk]; rfl
                          have hf_getD : found.getD block #[] = #[] := by
                            rw [Std.HashMap.getD_eq_getD_getElem?, hfound, hf_lk]; rfl
                          have hb_cont : idx.blocks.contains block = false := by
                            rw [Std.HashMap.contains_eq_isSome_getElem?, hblocks, hb_lk]; rfl
                          have han_cx := analyseRecursor_defCx_eq_pure ev (owner := owner) hrefs rec
                          have hst_blk := defCx_store_of_mem_pre ev (List.contains_iff_mem.mp hblk)
                          unfold Ix.CompileCert.ReaderIndex.candidate
                          dsimp only
                          simp only [hr_cont, Bool.false_eq_true, ↓reduceIte]
                          rw [han_cx, han]
                          dsimp only
                          rw [hc0]
                          dsimp only
                          rw [hst_blk, hbrec]
                          dsimp only
                          rw [hbi]
                          dsimp only
                          rw [hind0]
                          dsimp only
                          rw [hord]
                          simp only [↓reduceIte, hf_getD, hb_cont]
                          have hany_empty : (#[] : Array (Nat × ConstRef _root_.Address)).any
                              (·.1 == motive) = false := by
                            rw [← Array.any_toList]; rfl
                          simp only [hany_empty, Bool.false_eq_true, ↓reduceIte]
                          rw [id_pure]
                          dsimp only
                          refine ⟨?_, ?_, ?_⟩
                          · intro r
                            rw [Std.HashMap.getElem?_insert, List.lookup_cons]
                            by_cases he : r == ConstRef.member owner pos
                            · have hsym : (ConstRef.member owner pos == r) = true :=
                                beq_iff_eq.mpr (beq_iff_eq.mp he).symm
                              simp [he, hsym]
                            · have hsym : (ConstRef.member owner pos == r) = false :=
                                beq_eq_false_iff_ne.mpr fun h => he (beq_iff_eq.mpr h.symm)
                              rw [Bool.not_eq_true _ |>.mp he, hsym, hrecs r]; rfl
                          · intro b
                            rw [Std.HashMap.getElem?_insert, List.lookup_cons]
                            by_cases he : b == block
                            · have hsym : (block == b) = true :=
                                beq_iff_eq.mpr (beq_iff_eq.mp he).symm
                              simp [he, hsym, orderForList_eq, hsz_ind]
                            · have hsym : (block == b) = false :=
                                beq_eq_false_iff_ne.mpr fun h => he (beq_iff_eq.mpr h.symm)
                              rw [Bool.not_eq_true _ |>.mp he, hsym, hblocks b]; rfl
                          · intro b
                            rw [Std.HashMap.getElem?_insert, List.lookup_cons]
                            by_cases he : b == block
                            · have hsym : (block == b) = true :=
                                beq_iff_eq.mpr (beq_iff_eq.mp he).symm
                              have hpush : (#[] : Array (Nat × ConstRef _root_.Address)).push (motive, .member owner pos) =
                                  [(motive, .member owner pos)].toArray := by
                                apply Array.ext'; simp
                              simp [he, hsym, hpush]
                            · have hsym : (block == b) = false :=
                                beq_eq_false_iff_ne.mpr fun h => he (beq_iff_eq.mpr h.symm)
                              rw [Bool.not_eq_true _ |>.mp he, hsym, hfound b]; rfl

private theorem id_forIn_nil {α β : Type} (b : β) (f : α → β → Id (ForInStep β)) :
    forIn (m := Id) ([] : List α) b f = b := by
  rw [List.forIn_nil]; rfl

private theorem id_forIn_yield {α β : Type} (x : α) (xs : List α) (b y : β)
    (f : α → β → Id (ForInStep β)) (hy : f x b = .yield y) :
    forIn (m := Id) (x :: xs) b f = forIn (m := Id) xs y f := by
  rw [List.forIn_cons, hy]; rfl

private theorem id_forIn_done {α β : Type} (x : α) (xs : List α) (b y : β)
    (f : α → β → Id (ForInStep β)) (hd : f x b = .done y) :
    forIn (m := Id) (x :: xs) b f = y := by
  rw [List.forIn_cons, hd]; rfl

private theorem id_forIn_append {α β : Type} (f : α → β → Id (ForInStep β))
    (hy : ∀ x b, ∃ b', f x b = .yield b') :
    ∀ (l₁ l₂ : List α) (b : β),
      forIn (m := Id) (l₁ ++ l₂) b f = forIn (m := Id) l₂ (forIn (m := Id) l₁ b f) f
  | [], _, b => by rw [List.nil_append, id_forIn_nil]
  | x :: l₁, l₂, b => by
    obtain ⟨b', hb'⟩ := hy x b
    rw [List.cons_append, id_forIn_yield x (l₁ ++ l₂) b b' f hb',
        id_forIn_yield x l₁ b b' f hb', id_forIn_append f hy l₁ l₂ b']

private theorem forIn_recordStep_pre :
    ∀ (rs : List (_root_.Address × Ixon.Constant)) (s s' : PureIdx)
      (bs : Ix.CompileCert.ReaderIndex.BuildState),
      IdxMatches bs s →
      pureIndexRecords rs s = some s' →
      IdxMatches
        (forIn (m := Id) rs bs (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store)) s'
  | [], s, s', bs, hm, hp => by
    unfold pureIndexRecords at hp
    injection hp with hs
    subst hs
    rw [id_forIn_nil]
    exact hm
  | r :: rs, s, s', bs, hm, hp => by
    unfold pureIndexRecords at hp
    dsimp only [bind, Option.bind] at hp
    cases hrs : pureRecordIdxStep r s with
    | none => rw [hrs] at hp; cases hp
    | some smid =>
      rw [hrs] at hp
      rw [id_forIn_yield r rs bs _ _ rfl, ← Array.forIn_toList]
      unfold pureRecordIdxStep at hrs
      rw [recursorMembersFast_eq] at hrs
      cases hrm : (recursorMembers r.2).toList with
      | nil =>
        rw [hrm] at hrs
        rw [id_forIn_nil]
        injection hrs with hsm
        subst hsm
        exact forIn_recordStep_pre rs s s' bs hm hp
      | cons m tl =>
        cases tl with
        | cons _ _ => rw [hrm] at hrs; cases hrs
        | nil =>
          rw [hrm] at hrs
          have hmid := candidate_matches_of_pureCandStep ev hm hrs
          cases hcand : Ix.CompileCert.ReaderIndex.candidate (defCx ev).store r.1 r.2 m bs with
          | yield bs1 =>
            rw [id_forIn_yield _ _ _ _ _ hcand, id_forIn_nil]
            rw [hcand] at hmid
            exact forIn_recordStep_pre rs smid s' bs1 hmid hp
          | done bs1 =>
            rw [id_forIn_done _ _ _ _ _ hcand]
            rw [hcand] at hmid
            exact forIn_recordStep_pre rs smid s' bs1 hmid hp

private theorem forIn_recordStep_ev_noop :
    ∀ (rs : List (_root_.Address × Ixon.Constant))
      (bs : Ix.CompileCert.ReaderIndex.BuildState),
      (∀ p ∈ rs, ∃ d, p.2.info = .defn d) →
      forIn (m := Id) rs bs (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store) = bs
  | [], bs, _ => rfl
  | r :: rs, bs, hd => by
    obtain ⟨d, hrd⟩ := hd r List.mem_cons_self
    have hrm : recursorMembers r.2 = #[] := by simp [recursorMembers, hrd]
    rw [id_forIn_yield r rs bs _ _ rfl, hrm, ← Array.forIn_toList, id_forIn_nil]
    exact forIn_recordStep_ev_noop rs bs fun p hp => hd p (List.mem_cons_of_mem _ hp)

private theorem forIn_completeStep_recs :
    ∀ (es : List (_root_.Address × Array (Nat × ConstRef _root_.Address))) (idx : RecIndex),
      (forIn (m := Id) es idx Ix.CompileCert.ReaderIndex.completeStep).recs = idx.recs
  | [], _ => rfl
  | e :: es, idx => by
    rw [id_forIn_yield e es idx _ _ rfl]
    exact forIn_completeStep_recs es _

private theorem qsort_singleton {α : Type} (x : α) (lt : α → α → Bool) :
    #[x].qsort lt = #[x] := by
  have hp : (#[x].qsort lt).toList.Perm [x] :=
    Array.perm_iff_toList_perm.mp (Ix.CompileCert.Canon.qsort_perm #[x] lt)
  apply Array.ext'
  exact List.perm_singleton.mp hp

private theorem forIn_completeStep_block
    {b : _root_.Address} {order : Array Nat} {m : Nat} {ref : ConstRef _root_.Address}
    {found : Ix.CompileCert.ReaderIndex.Found}
    (hf : found[b]? = some #[(m, ref)]) :
    ∀ (es : List (_root_.Address × Array (Nat × ConstRef _root_.Address))) (idx : RecIndex),
      (∀ e ∈ es, found[e.1]? = some e.2) →
      (idx.blocks.getD b default).order = order →
      ((b, #[(m, ref)]) ∈ es ∨ idx.blocks[b]? = some ⟨order, #[ref]⟩) →
      (forIn (m := Id) es idx Ix.CompileCert.ReaderIndex.completeStep).blocks[b]? =
        some ⟨order, #[ref]⟩
  | [], idx, _, _, hor => by
    rcases hor with hmem | hdone
    · cases hmem
    · rw [id_forIn_nil]; exact hdone
  | (k, arr) :: es, idx, hes, hord, hor => by
    rw [id_forIn_yield (k, arr) es idx _ _ rfl]
    dsimp only
    by_cases hkb : k = b
    · subst hkb
      have harr_some := hes (k, arr) List.mem_cons_self
      rw [hf] at harr_some
      injection harr_some with harr
      subst harr
      rw [qsort_singleton]
      have hmap : (#[(m, ref)].map (·.2)) = #[ref] := by
        apply Array.ext'; simp
      rw [hmap]
      let shape' : BlockShape := { (idx.blocks.getD k default) with recs := #[ref] }
      let idx' : RecIndex := { idx with blocks := idx.blocks.insert k shape' }
      have hdone : idx'.blocks[k]? = some ⟨order, #[ref]⟩ := by
        show (idx.blocks.insert k shape')[k]? = _
        rw [Std.HashMap.getElem?_insert_self]
        dsimp only [shape']
        cases hgd : idx.blocks.getD k default with
        | mk ord rcs =>
          rw [hgd] at hord
          dsimp only at hord ⊢
          rw [hord]
      have hord' : (idx'.blocks.getD k default).order = order := by
        rw [Std.HashMap.getD_eq_getD_getElem?, hdone]; rfl
      exact forIn_completeStep_block hf es idx'
        (fun e he => hes e (List.mem_cons_of_mem _ he)) hord' (.inr hdone)
    · let shape' : BlockShape :=
        { (idx.blocks.getD k default) with recs := (arr.qsort (fun l r => l.1 < r.1)).map (·.2) }
      let idx' : RecIndex := { idx with blocks := idx.blocks.insert k shape' }
      have hsame : idx'.blocks[b]? = idx.blocks[b]? := by
        show (idx.blocks.insert k shape')[b]? = _
        simp [Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.mpr hkb]
      have hord' : (idx'.blocks.getD b default).order = order := by
        rw [Std.HashMap.getD_eq_getD_getElem?, hsame, ← Std.HashMap.getD_eq_getD_getElem?]
        exact hord
      have hor' : (b, #[(m, ref)]) ∈ es ∨ idx'.blocks[b]? = some ⟨order, #[ref]⟩ := by
        rcases hor with hmem | hdone
        · rcases List.mem_cons.mp hmem with heq | htl
          · injection heq with hbk; exact absurd hbk.symm hkb
          · exact .inl htl
        · rw [hsame]; exact .inr hdone
      exact forIn_completeStep_block hf es idx'
        (fun e he => hes e (List.mem_cons_of_mem _ he)) hord' hor'

include hev_defn in
private theorem collected_matches_purePreIdx {s : PureIdx} (hs : purePreIdx? = some s) :
    IdxMatches
      (forIn (m := Id) (indexedRecords (defCx ev).store committedPrelude ev)
        (({} : RecIndex), ({} : Ix.CompileCert.ReaderIndex.Found))
        (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store)) s := by
  simp only [indexedRecords, filter_committedPrelude_inputIndexed ev]
  rw [← Array.forIn_toList, Array.toList_append,
      id_forIn_append (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store) (fun _ _ => ⟨_, rfl⟩),
      show committedPrelude.toList = committedPreludeList from rfl]
  have hinit : IdxMatches (({} : RecIndex), ({} : Ix.CompileCert.ReaderIndex.Found)) (PureIdx.mk [] [] []) :=
    ⟨fun _ => Std.HashMap.getElem?_empty,
     fun _ => Std.HashMap.getElem?_empty,
     fun _ => Std.HashMap.getElem?_empty⟩
  have hpre := forIn_recordStep_pre ev committedPreludeList (PureIdx.mk [] [] []) s _ hinit hs
  rw [forIn_recordStep_ev_noop ev _ _ (fun p hp => by
    rw [Array.toList_filter] at hp
    exact hev_defn p (List.mem_of_mem_filter hp))]
  exact hpre

include hev_defn in
private theorem defCx_index_recs_of_pure {ref : ConstRef _root_.Address} {entry : RecEntry}
    (h : pureRecsLookup ref = some entry) :
    (defCx ev).index.recs[ref]? = some entry := by
  unfold pureRecsLookup at h
  cases hs : purePreIdx? with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    dsimp only [bind, Option.bind] at h
    rw [lookupConstRefFast_eq] at h
    rw [defCx_index_eq ev, ← Ix.CompileCert.ReaderIndex.run_eq]
    unfold Ix.CompileCert.ReaderIndex.run
    rw [forIn_completeStep_recs]
    exact (collected_matches_purePreIdx ev hev_defn hs).1 ref |>.trans h

include hev_defn in
private theorem defCx_index_blocks_of_pure {b : _root_.Address}
    {orderL : List Nat} {recsL : List (ConstRef _root_.Address)}
    (h : pureBlocksLookup b = some (orderL, recsL)) :
    (defCx ev).index.blocks[b]? = some ⟨orderL.toArray, recsL.toArray⟩ := by
  unfold pureBlocksLookup at h
  cases hs : purePreIdx? with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    dsimp only [bind, Option.bind] at h
    simp only [lookupAddrFast_eq] at h
    cases hob : s.blocks.lookup b with
    | none => rw [hob] at h; cases h
    | some ordL =>
      rw [hob] at h
      dsimp only at h
      cases hfb : s.found.lookup b with
      | none => rw [hfb] at h; cases h
      | some foundL =>
        rw [hfb] at h
        dsimp only at h
        injection h with hp
        injection hp with h1 h2
        subst h1; subst h2
        have hsing := purePreIdx_found_singletons
        unfold purePreIdxFoundSingletonsBool at hsing
        rw [hs] at hsing
        have hmem_f := mem_of_lookup_eq_some hfb
        have hlen : foundL.length = 1 :=
          beq_iff_eq.mp (List.all_eq_true.mp hsing (b, foundL) hmem_f)
        obtain ⟨⟨m, ref⟩, rfl⟩ : ∃ x, foundL = [x] := by
          cases foundL with
          | nil => cases hlen
          | cons x tl =>
            cases tl with
            | nil => exact ⟨x, rfl⟩
            | cons _ _ => simp at hlen
        have hcm := collected_matches_purePreIdx ev hev_defn hs
        rw [defCx_index_eq ev, ← Ix.CompileCert.ReaderIndex.run_eq]
        unfold Ix.CompileCert.ReaderIndex.run
        let collected := forIn (m := Id) (indexedRecords (defCx ev).store committedPrelude ev)
          (({} : RecIndex), ({} : Ix.CompileCert.ReaderIndex.Found))
          (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store)
        have hf_col : collected.2[b]? = some #[(m, ref)] := by
          rw [hcm.2.2 b, hfb]; rfl
        have hb_col : collected.1.blocks[b]? = some ⟨ordL.toArray, #[]⟩ := by
          rw [hcm.2.1 b, hob]; rfl
        have hord_col : (collected.1.blocks.getD b default).order = ordL.toArray := by
          rw [Std.HashMap.getD_eq_getD_getElem?, hb_col]; rfl
        have hmem_toList : (b, #[(m, ref)]) ∈ collected.2.toList :=
          Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hf_col
        exact forIn_completeStep_block hf_col collected.2.toList collected.1
          (fun e he => Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he)
          hord_col (.inl hmem_toList)

/-! ### Shape-only expression and prelude stream soundness -/

include hev_defn in
private theorem pureMemberKeyOpt_sound {r : ConstRef _root_.Address} {k : CName .anon}
    (h : pureMemberKeyOpt r = some k) :
    (defCx ev).memberKey r = .ok k :=
  Ctx.memberKey_of_role (defCx_roles_of_pure ev hev_defn h)

include hev_defn in
private theorem pureKeyAtOpt_sound {a : _root_.Address} {k : CName .anon}
    (h : pureKeyAtOpt a = some k) :
    (defCx ev).keyAt a = .ok k := by
  unfold pureKeyAtOpt at h
  rw [containsAddrFast_eq] at h
  cases hpa : committedPreAddrs.contains a with
  | false => rw [hpa] at h; cases h
  | true =>
    simp only [hpa, ↓reduceIte] at h
    have ha_mem : a ∈ committedPreAddrs := List.contains_iff_mem.mp hpa
    cases hr : resolve preStorePure a with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      dsimp only at h
      rw [Ctx.keyAt_eq_ok]
      unfold keyOfAddress
      rw [resolve_defCx_of_mem_pre ev ha_mem, hr]
      dsimp only [bind, Option.bind]
      rw [defCx_roles_of_pure ev hev_defn h]

private def MatchesShape (e : CExpr .anon) (sh : ExprShape) : Prop :=
  piTeleLen e = sh.piLen ∧
  match sh.piSort? with
  | some u => e.piResult = .sort u ∧ e.piSortTeleLen? = some sh.piLen
  | none => e.piSortTeleLen? = none ∧ ∀ u, e.piResult ≠ .sort u

private theorem nth?_isSome_of_lt {α : Type} :
    ∀ (l : List α) (n : Nat), n < l.length → ∃ x, l[n]? = some x
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, n + 1, h => nth?_isSome_of_lt xs n (Nat.lt_of_succ_lt_succ h)

private theorem pureLevelsOk_sound (ecx : ECx .anon) (univs : List CLevel)
    (hu_eq : ecx.univs = univs.toArray) :
    ∀ (l : List UInt64), pureLevelsOk univs.length l = true → ∃ ls, l.mapM ecx.level = .ok ls
  | [], _ => ⟨[], rfl⟩
  | u :: us, h => by
    unfold pureLevelsOk at h
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨lv, hlv⟩ := nth?_isSome_of_lt univs u.toNat h.1
    have hlev : ecx.level u = .ok lv := by
      unfold ECx.level
      rw [hu_eq, List.getElem?_toArray, hlv]
      rfl
    obtain ⟨tail, htail⟩ := pureLevelsOk_sound ecx univs hu_eq us h.2
    refine ⟨lv :: tail, ?_⟩
    simp only [List.mapM_cons, hlev, htail, bind, Except.bind, pure, Except.pure]

include hev_defn in
private theorem pureConvExprShape_sound {src : Ixon.Constant}
    {univs : List CLevel} {selfOk : Nat → Bool}
    {rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i, selfOk i = true → ∃ rm k, rself i = some rm ∧ rm = .ok k)
    {ptbl : List (Option ExprShape)} {rtbl : Array (ReadM (CExpr .anon))}
    (htbl : ∀ (i : Nat) (sh : ExprShape), nth? ptbl i = some (some sh) →
      ∃ e, rtbl[i]? = some (Except.ok e) ∧ MatchesShape e sh) :
    ∀ (expr : Ixon.Expr) {sh : ExprShape},
      pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl expr = some sh →
      ∃ out, convExpr ⟨defCx ev, src, univs.toArray, rself⟩ rtbl expr = .ok out ∧
        MatchesShape out sh
  | .var i, _, h => by
    unfold pureConvExprShape at h
    injection h with hsh; subst hsh
    refine ⟨.bvar i.toNat, ?_, rfl, rfl, fun _ hc => by cases hc⟩
    rw [convExpr, Ix.Kernel.Expr.mkBvar_eq]
    rfl
  | .sort i, _, h => by
    unfold pureConvExprShape at h
    rw [nth?_eq] at h
    cases hu : univs[i.toNat]? with
    | none => rw [hu] at h; cases h
    | some u =>
      rw [hu] at h
      injection h with hsh; subst hsh
      refine ⟨.sort u, ?_, rfl, rfl, rfl⟩
      unfold convExpr ECx.level
      rw [List.getElem?_toArray, hu]
      rfl
  | .ref i us, _, h => by
    unfold pureConvExprShape at h
    rw [nth?_eq, Array.getElem?_toList] at h
    cases href : src.refs[i.toNat]? with
    | none => rw [href] at h; cases h
    | some a =>
      rw [href] at h
      dsimp only at h
      cases hka : pureKeyAtOpt a with
      | none => rw [hka] at h; cases h
      | some k =>
        rw [hka] at h
        dsimp only at h
        cases hlo : pureLevelsOk univs.length us.toList with
        | false => rw [hlo] at h; cases h
        | true =>
          simp only [hlo, ↓reduceIte, Option.some.injEq] at h
          subst h
          have hreal_k := pureKeyAtOpt_sound ev hev_defn hka
          obtain ⟨ls, hls⟩ := pureLevelsOk_sound ⟨defCx ev, src, univs.toArray, rself⟩ univs rfl us.toList hlo
          refine ⟨.const k ls, ?_, rfl, rfl, fun _ hc => by cases hc⟩
          unfold convExpr ECx.keyAt ECx.levels
          simp only [href, hreal_k, hls, bind, Except.bind, pure, Except.pure]
  | .recur i us, _, h => by
    unfold pureConvExprShape at h
    cases hso : selfOk i.toNat with
    | false => simp [hso] at h
    | true =>
      cases hlo : pureLevelsOk univs.length us.toList with
      | false => simp [hso, hlo] at h
      | true =>
        simp only [hso, hlo, Bool.and_self, ↓reduceIte, Option.some.injEq] at h
        subst h
        obtain ⟨rm, k, hrs, hrm⟩ := hself i.toNat hso
        obtain ⟨ls, hls⟩ := pureLevelsOk_sound ⟨defCx ev, src, univs.toArray, rself⟩ univs rfl us.toList hlo
        refine ⟨.const k ls, ?_, rfl, rfl, fun _ hc => by cases hc⟩
        unfold convExpr ECx.levels
        simp only [hrs, hrm, hls, bind, Except.bind, pure, Except.pure]
  | .prj i field v, _, h => by
    unfold pureConvExprShape at h
    rw [nth?_eq, Array.getElem?_toList] at h
    cases href : src.refs[i.toNat]? with
    | none => rw [href] at h; cases h
    | some a =>
      rw [href] at h
      dsimp only at h
      cases hka : pureKeyAtOpt a with
      | none => rw [hka] at h; cases h
      | some k =>
        rw [hka] at h
        cases hv : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl v with
        | none => rw [hv] at h; cases h
        | some sv =>
          rw [hv] at h
          injection h with hsh; subst hsh
          have hreal_k := pureKeyAtOpt_sound ev hev_defn hka
          obtain ⟨ve, hve, -⟩ := pureConvExprShape_sound hself htbl v hv
          refine ⟨.proj k field.toNat ve, ?_, rfl, rfl, fun _ hc => by cases hc⟩
          unfold convExpr ECx.keyAt
          simp only [href, hreal_k, hve, bind, Except.bind, pure, Except.pure]
  | .str _, _, h => by cases h
  | .nat _, _, h => by cases h
  | .app f a, _, h => by
    unfold pureConvExprShape at h
    cases hf : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl f with
    | none => rw [hf] at h; cases h
    | some sf =>
      rw [hf] at h
      cases ha : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl a with
      | none => rw [ha] at h; cases h
      | some sa =>
        rw [ha] at h
        injection h with hsh; subst hsh
        obtain ⟨fe, hfe, -⟩ := pureConvExprShape_sound hself htbl f hf
        obtain ⟨ae, hae, -⟩ := pureConvExprShape_sound hself htbl a ha
        refine ⟨.app fe ae, ?_, rfl, rfl, fun _ hc => by cases hc⟩
        simp only [convExpr, hfe, hae, bind, Except.bind, pure, Except.pure]
  | .lam t b, _, h => by
    unfold pureConvExprShape at h
    cases ht : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl t with
    | none => rw [ht] at h; cases h
    | some st =>
      rw [ht] at h
      cases hb : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl b with
      | none => rw [hb] at h; cases h
      | some sb =>
        rw [hb] at h
        injection h with hsh; subst hsh
        obtain ⟨te, hte, -⟩ := pureConvExprShape_sound hself htbl t ht
        obtain ⟨be, hbe, -⟩ := pureConvExprShape_sound hself htbl b hb
        refine ⟨.lam te be Ix.Kernel.BinderMeta.leanNever, ?_, rfl, rfl, fun _ hc => by cases hc⟩
        simp only [convExpr, hte, hbe, bind, Except.bind, pure, Except.pure]
  | .all t b, _, h => by
    unfold pureConvExprShape at h
    cases ht : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl t with
    | none => rw [ht] at h; cases h
    | some st =>
      rw [ht] at h
      cases hb : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl b with
      | none => rw [hb] at h; cases h
      | some sb =>
        rw [hb] at h
        injection h with hsh; subst hsh
        obtain ⟨te, hte, -⟩ := pureConvExprShape_sound hself htbl t ht
        obtain ⟨be, hbe, hb_len, hb_sort⟩ := pureConvExprShape_sound hself htbl b hb
        refine ⟨.forallE te be Ix.Kernel.BinderMeta.leanNever, ?_, ?_⟩
        · simp only [convExpr, hte, hbe, bind, Except.bind, pure, Except.pure]
        · refine ⟨by simp [piTeleLen, hb_len], ?_⟩
          cases hps : sb.piSort? with
          | some u =>
            rw [hps] at hb_sort
            dsimp only at hb_sort ⊢
            exact ⟨by simp [Ix.Kernel.Expr.piResult, hb_sort.1],
              by simp [Ix.Kernel.Expr.piSortTeleLen?, hb_sort.2]⟩
          | none =>
            rw [hps] at hb_sort
            dsimp only at hb_sort ⊢
            exact ⟨by simp [Ix.Kernel.Expr.piSortTeleLen?, hb_sort.1],
              fun u => by simp [Ix.Kernel.Expr.piResult]; exact hb_sort.2 u⟩
  | .letE nonDep mode t v b, _, h => by
    unfold pureConvExprShape at h
    cases ht : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl t with
    | none => rw [ht] at h; cases h
    | some st =>
      rw [ht] at h
      cases hv : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl v with
      | none => rw [hv] at h; cases h
      | some sv =>
        rw [hv] at h
        cases hb : pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl b with
        | none => rw [hb] at h; cases h
        | some sb =>
          rw [hb] at h
          injection h with hsh; subst hsh
          obtain ⟨te, hte, -⟩ := pureConvExprShape_sound hself htbl t ht
          obtain ⟨ve, hve, -⟩ := pureConvExprShape_sound hself htbl v hv
          obtain ⟨be, hbe, -⟩ := pureConvExprShape_sound hself htbl b hb
          refine ⟨.letE te ve be { nonDep }, ?_, rfl, rfl, fun _ hc => by cases hc⟩
          simp only [convExpr, hte, hve, hbe, bind, Except.bind, pure, Except.pure]
  | .share i, _, h => by
    unfold pureConvExprShape at h
    cases hget : nth? ptbl i.toNat with
    | none => rw [hget] at h; cases h
    | some opt =>
      rw [hget] at h
      cases opt with
      | none => cases h
      | some sh' =>
        injection h with hsh; subst hsh
        obtain ⟨e, hr, hm⟩ := htbl i.toNat sh' hget
        exact ⟨e, by simp [convExpr, hr], hm⟩

private theorem nth?_append_singleton {α : Type} :
    ∀ (l : List α) (x : α) (i : Nat),
      nth? (l ++ [x]) i = if i = l.length then some x else nth? l i
  | [], _, 0 => rfl
  | [], _, _ + 1 => rfl
  | _ :: _, _, 0 => rfl
  | _ :: xs, x, i + 1 => by
    simp only [List.cons_append, nth?, List.length_cons]
    rw [nth?_append_singleton xs x i]
    by_cases h : i = xs.length <;> simp [h]

include hev_defn in
private theorem foldl_sharing_shape_tbl {src : Ixon.Constant}
    {univs : List CLevel} {selfOk : Nat → Bool}
    {rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i, selfOk i = true → ∃ rm k, rself i = some rm ∧ rm = .ok k) :
    ∀ (es : List Ixon.Expr) (ptbl : List (Option ExprShape)) (rtbl : Array (ReadM (CExpr .anon))),
      ptbl.length = rtbl.size →
      (∀ (i : Nat) (sh : ExprShape), nth? ptbl i = some (some sh) →
        ∃ e, rtbl[i]? = some (Except.ok e) ∧ MatchesShape e sh) →
      ∀ (i : Nat) (sh : ExprShape),
        nth? (pureBuildShapeTbl ⟨src.refs.toList, univs, selfOk⟩ es ptbl) i = some (some sh) →
        ∃ e,
          (es.foldl (fun tbl entry =>
            tbl.push (convExpr ⟨defCx ev, src, univs.toArray, rself⟩ tbl entry)) rtbl)[i]? =
            some (Except.ok e) ∧
          MatchesShape e sh
  | [], _, _, _, htbl => htbl
  | entry :: es, ptbl, rtbl, hsz, htbl => by
    rw [List.foldl_cons]
    dsimp only [pureBuildShapeTbl]
    refine foldl_sharing_shape_tbl hself es
      (ptbl ++ [pureConvExprShape ⟨src.refs.toList, univs, selfOk⟩ ptbl entry])
      (rtbl.push (convExpr ⟨defCx ev, src, univs.toArray, rself⟩ rtbl entry))
      (by simp [hsz]) ?_
    intro i sh hi
    rw [nth?_append_singleton] at hi
    rw [Array.getElem?_push]
    by_cases heq : i = ptbl.length
    · simp only [heq, ↓reduceIte, Option.some.injEq] at hi
      simp only [← hsz, heq, ↓reduceIte]
      obtain ⟨out, hout, hm⟩ := pureConvExprShape_sound ev hev_defn hself htbl entry hi
      exact ⟨out, congrArg some hout, hm⟩
    · simp only [heq, ↓reduceIte] at hi
      simp only [← hsz, heq, ↓reduceIte]
      exact htbl i sh hi

include hev_defn in
private theorem pureReadExprShape_sound {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {selfOk : Nat → Bool} {rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i, selfOk i = true → ∃ rm k, rself i = some rm ∧ rm = .ok k)
    {expr : Ixon.Expr} {sh : ExprShape}
    (h : pureReadExprShape src param selfOk expr = some sh) :
    ∃ out, (MemberReader.mk' (defCx ev) src param rself).read expr = .ok out ∧
      MatchesShape out sh := by
  unfold pureReadExprShape at h
  dsimp only at h
  have hunivs : (src.univs.toList.map (convUniv param)).toArray = src.univs.map (convUniv param) := by
    apply Array.ext'; simp
  rw [Ix.CompileCert.SharingRoots.memberReader_eq]
  unfold MemberReader.read Ix.CompileCert.SharingRoots.expressionContext
    Ix.CompileCert.SharingRoots.buildTable
  dsimp only
  rw [← hunivs]
  exact pureConvExprShape_sound ev hev_defn hself
    (foldl_sharing_shape_tbl ev hev_defn hself src.sharing.toList [] #[] rfl
      (fun i _ h0 => by cases i <;> cases h0))
    expr h

include hev_defn in
private theorem pureReadRecRulesOk_sound {src : Ixon.Constant}
    {param : Nat → Ix.Kernel.LevelParam}
    {selfOk : Nat → Bool} {rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i, selfOk i = true → ∃ rm k, rself i = some rm ∧ rm = .ok k)
    {mb : _root_.Address} {mi : Nat} :
    ∀ (l : List (Ixon.RecursorRule × Nat)) (acc : List (Ix.Kernel.RecRule .anon)),
      pureReadRecRulesOk src param selfOk mb mi l = true →
      ∃ tail,
        forIn (m := ReadM) l acc (fun (rule, k) rules => do
          let ck ← (defCx ev).memberKey (.ctor mb mi k)
          let rhs ← (MemberReader.mk' (defCx ev) src param rself).read rule.rhs
          pure (.yield (rules ++ [Ix.Kernel.RecRule.mk ck rule.fields.toNat 0 .inert rhs false false false]))) =
          .ok (acc ++ tail)
  | [], acc, _ => ⟨[], by simp [pure, Except.pure]⟩
  | (rule, k) :: rest, acc, h => by
    unfold pureReadRecRulesOk at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hck_some, hrhs_some⟩, hrest⟩ := h
    cases hck : pureMemberKeyOpt (.ctor mb mi k) with
    | none => rw [hck] at hck_some; cases hck_some
    | some ck =>
      cases hrhs : pureReadExprShape src param selfOk rule.rhs with
      | none => rw [hrhs] at hrhs_some; cases hrhs_some
      | some rsh =>
        have hck' := pureMemberKeyOpt_sound ev hev_defn hck
        obtain ⟨rhs, hrhs', -⟩ := pureReadExprShape_sound ev hev_defn hself hrhs
        let r0 := Ix.Kernel.RecRule.mk ck rule.fields.toNat 0 .inert rhs false false false
        obtain ⟨rtail, htail⟩ := pureReadRecRulesOk_sound hself rest (acc ++ [r0]) hrest
        refine ⟨r0 :: rtail, ?_⟩
        have hstep : (do
            let ck' ← (defCx ev).memberKey (.ctor mb mi k)
            let rhs' ← (MemberReader.mk' (defCx ev) src param rself).read rule.rhs
            pure (f := ReadM) (ForInStep.yield (acc ++
              [Ix.Kernel.RecRule.mk ck' rule.fields.toNat 0 .inert rhs' false false false]))) =
            Except.ok (ForInStep.yield (acc ++ [r0])) := by
          simp only [hck', hrhs', bind, Except.bind, pure, Except.pure, r0]
        rw [List.forIn_cons]
        dsimp only
        rw [hstep, except_ok_bind]
        dsimp only
        rw [htail, List.append_assoc, List.singleton_append]

include hev_defn in
private theorem pureReadRecursorKeyCounts_sound {blockLps : List Ix.Kernel.LevelParam}
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    {key : CName .anon} {rcounts : RecCounts}
    (h : pureReadRecursorKeyCounts blockLps ref entry = some (key, rcounts)) :
    ∃ (typ : CExpr .anon) (rules : List (Ix.Kernel.RecRule .anon)),
      readRecursor (defCx ev) blockLps ref entry =
        .ok (⟨key, recLps entry.large blockLps, typ⟩, rcounts, rules) := by
  unfold pureReadRecursorKeyCounts at h
  cases ref with
  | ctor _ _ _ => cases h
  | member rOwner j =>
    dsimp only at h
    rw [containsAddrFast_eq] at h
    cases hro : committedPreAddrs.contains rOwner with
    | false => rw [hro] at h; cases h
    | true =>
      simp only [hro, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rc, hrc, h⟩ := option_bind_eq_some h
      obtain ⟨⟨fstIdx, r⟩, hfind0, h⟩ := option_bind_eq_some h
      have hfind : (recursorMembers rc).find? (·.1 == j) = some (fstIdx, r) := by
        rwa [recursorMembersFast_eq, Array.find?_toList] at hfind0
      dsimp only at h
      cases hu : r.isUnsafe with
      | true => rw [hu] at h; cases h
      | false =>
        simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨rkey, hkey, h⟩ := option_bind_eq_some h
        obtain ⟨tsh, htyp, h⟩ := option_bind_eq_some h
        cases hmaj : entry.major with
        | ctor _ _ _ => rw [hmaj] at h; cases h
        | member mb mi =>
          rw [hmaj] at h
          dsimp only at h
          rw [containsAddrFast_eq] at h
          cases hmb : committedPreAddrs.contains mb with
          | false => rw [hmb] at h; cases h
          | true =>
            simp only [hmb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨major, hind, h⟩ := option_bind_eq_some h
            rw [Array.length_toList, Array.length_toList] at h
            cases hsz : (major.ctors.size == r.rules.size) with
            | false => rw [hsz] at h; cases h
            | true =>
              simp only [hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              rw [← Array.toList_zipIdx] at h
              obtain ⟨hrok, h⟩ := ite_not_eq_some h
              injection h with hpair
              rcases Prod.mk.inj hpair with ⟨hkeq, hceq⟩
              have hkey' := pureMemberKeyOpt_sound ev hev_defn hkey
              let rself : Nat → Option (ReadM (CName .anon)) := fun i => match rc.info with
                | .muts rms =>
                  if i < rms.size then some ((defCx ev).memberKey (.member rOwner i))
                  else none
                | _ => if i == 0 then some (pure rkey) else none
              have h_both :
                  (∃ out, (MemberReader.mk' (defCx ev) rc (recParam (recLps entry.large blockLps)) rself).read r.typ = .ok out) ∧
                  (∃ tail, forIn (m := ReadM) r.rules.zipIdx.toList [] (fun (rule, k) rules => do
                    let ck ← (defCx ev).memberKey (.ctor mb mi k)
                    let rhs ← (MemberReader.mk' (defCx ev) rc (recParam (recLps entry.large blockLps)) rself).read rule.rhs
                    pure (.yield (rules ++ [Ix.Kernel.RecRule.mk ck rule.fields.toNat 0 .inert rhs false false false]))) =
                      .ok ([] ++ tail)) := by
                refine ⟨let ⟨o, ho, _⟩ := pureReadExprShape_sound ev hev_defn ?hself htyp; ⟨o, ho⟩,
                        pureReadRecRulesOk_sound ev hev_defn ?hself r.rules.zipIdx.toList [] hrok⟩
                case hself =>
                  intro i hso
                  dsimp only [rself]
                  cases hinfo : rc.info with
                  | muts rms =>
                    rw [hinfo] at hso
                    dsimp only at hso
                    rw [Array.length_toList, Bool.and_eq_true, decide_eq_true_eq] at hso
                    simp only [hso.1, ↓reduceIte]
                    cases hmki : pureMemberKeyOpt (.member rOwner i) with
                    | none => rw [hmki] at hso; cases hso.2
                    | some ki =>
                      exact ⟨_, ki, rfl, pureMemberKeyOpt_sound ev hev_defn hmki⟩
                  | _ =>
                    rw [hinfo] at hso
                    dsimp only at hso
                    simp only [hso, ↓reduceIte]
                    exact ⟨_, rkey, rfl, rfl⟩
              obtain ⟨⟨typ, htyp'⟩, ⟨rules, hloop⟩⟩ := h_both
              dsimp only [rself] at htyp' hloop
              have hst_ro := defCx_store_of_mem_pre ev (List.contains_iff_mem.mp hro)
              have hind_cx : inductiveAt (defCx ev).store (.member mb mi) = some major := by
                unfold inductiveAt at hind ⊢
                dsimp only at hind ⊢
                rw [defCx_store_of_mem_pre ev (List.contains_iff_mem.mp hmb)]
                exact hind
              subst hkeq hceq
              refine ⟨typ, rules, ?_⟩
              unfold readRecursor
              simp only [hst_ro, hrc, hfind, hu, Bool.false_eq_true, ↓reduceIte]
              simp only [hkey', bind, Except.bind]
              split
              · rename_i err heq
                exact absurd (htyp'.symm.trans heq) (by simp)
              · rename_i v heq
                have hv : v = typ := Except.ok.inj (heq.symm.trans htyp')
                subst hv
                simp only [hmaj, hind_cx, hsz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                rw [← Array.forIn_toList]
                split
                · rename_i err heq2
                  exact absurd (hloop.symm.trans heq2) (by simp)
                · rename_i rules' heq2
                  rw [List.nil_append] at hloop
                  have hr : rules' = rules := Except.ok.inj (heq2.symm.trans hloop)
                  rw [hr]
                  rfl

include hev_defn in
private theorem pureReadCtorShapes_sound {owner : _root_.Address} {src : Ixon.Constant}
    {selfOk : Nat → Bool} {rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i, selfOk i = true → ∃ rm k, rself i = some rm ∧ rm = .ok k)
    {nPd : Nat} :
    ∀ (l : List (Ixon.Constructor × Nat))
      (accC : Array (CVal .anon × Nat × Nat)) (accN : List (CName .anon))
      {pairs : List (CName .anon × Nat)},
      pureReadCtorShapes owner src selfOk nPd l = some pairs →
      ∃ (outC : List (CVal .anon × Nat × Nat)),
        forIn (m := ReadM) l (accC, accN)
          (Ix.CompileCert.InductiveReading.ctorStep (defCx ev) owner
            (MemberReader.mk' (defCx ev) src id rself) nPd 0) =
          .ok (accC ++ outC.toArray, accN ++ pairs.map Prod.fst) ∧
        outC.map (fun (cv, _, nF) => (cv.name, nF)) = pairs
  | [], accC, accN, _, h => by
    unfold pureReadCtorShapes at h
    injection h with hp; subst hp
    exact ⟨[], ⟨by simp [pure, Except.pure], rfl⟩⟩
  | (ctor, j) :: rest, accC, accN, _, h => by
    unfold pureReadCtorShapes at h
    dsimp only [bind, Option.bind] at h
    cases hcj : (ctor.cidx.toNat == j) with
    | false => rw [hcj] at h; cases h
    | true =>
      simp only [hcj, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hcu : ctor.isUnsafe with
      | true => rw [hcu] at h; cases h
      | false =>
        simp only [hcu, Bool.false_eq_true, ↓reduceIte] at h
        cases hck : pureMemberKeyOpt (.ctor owner 0 j) with
        | none => rw [hck] at h; cases h
        | some ck =>
          rw [hck] at h
          dsimp only at h
          cases hcsh : pureReadExprShape src id selfOk ctor.typ with
          | none => rw [hcsh] at h; cases h
          | some csh =>
            rw [hcsh] at h
            dsimp only at h
            cases hfl : (nPd + ctor.fields.toNat == csh.piLen) with
            | false => rw [hfl] at h; cases h
            | true =>
              simp only [hfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
              cases htail : pureReadCtorShapes owner src selfOk nPd rest with
              | none => rw [htail] at h; cases h
              | some tailP =>
                rw [htail] at h
                injection h with hp; subst hp
                have hck' := pureMemberKeyOpt_sound ev hev_defn hck
                obtain ⟨cty, hcty', hcty_len, -⟩ := pureReadExprShape_sound ev hev_defn hself hcsh
                rw [← hcty_len] at hfl
                let headC : CVal .anon × Nat × Nat :=
                  (⟨ck, List.range ctor.lvls.toNat, cty⟩, ctor.params.toNat, ctor.fields.toNat)
                obtain ⟨tailC, hfor_tail, hmap_tail⟩ :=
                  pureReadCtorShapes_sound hself rest (accC.push headC) (accN ++ [ck]) htail
                refine ⟨headC :: tailC, ?_, ?_⟩
                · have hstep : Ix.CompileCert.InductiveReading.ctorStep (defCx ev) owner
                      (MemberReader.mk' (defCx ev) src id rself) nPd 0 (ctor, j) (accC, accN) =
                      .ok (.yield (accC.push headC, accN ++ [ck])) := by
                    simp only [Ix.CompileCert.InductiveReading.ctorStep, hcj, ↓reduceIte, hcu,
                      Bool.false_eq_true, hck', hcty', hfl, bind, Except.bind, pure, Except.pure,
                      headC]
                  rw [List.forIn_cons, hstep]
                  dsimp only [bind, Except.bind]
                  rw [hfor_tail]
                  have hap : accC.push headC ++ tailC.toArray = accC ++ (headC :: tailC).toArray := by
                    apply Array.ext'
                    simp [List.append_assoc]
                  rw [hap, List.map_cons, List.append_assoc, List.singleton_append]
                · simp [headC, hmap_tail]

private theorem levelIsZeroFast_sound {s : Ix.Kernel.Level} {b : Bool}
    (h : levelIsZeroFast s = some b) :
    Ix.Kernel.Level.isEquiv s .zero = some b := by
  cases s with
  | zero =>
    injection h with hb; subst hb; rfl
  | param p =>
    injection h with hb; subst hb
    have hleq : Ix.Kernel.Level.leq (.param p) .zero = some false := by
      unfold Ix.Kernel.Level.leq
      rw [show Ix.Kernel.Level.defaultFuel = 9999 + 1 from rfl]
      unfold Ix.Kernel.Level.leqCore
      have hlt0 : ¬ ((0 : Int) < 0) := by decide
      simp only [Ix.Kernel.Level.simplify, reduceCtorEq, false_and, ↓reduceIte, hlt0, and_false]
      unfold Ix.Kernel.Level.rest
      rfl
    unfold Ix.Kernel.Level.isEquiv
    have h1 : (Ix.Kernel.Level.param p == .zero) = false :=
      beq_eq_false_iff_ne.mpr (by simp)
    simp only [h1, Bool.false_eq_true, ↓reduceIte, Ix.Kernel.Level.simplify, reduceCtorEq,
      hleq, bind, Option.bind, pure]
  | succ l =>
    injection h with hb; subst hb
    have hleq : Ix.Kernel.Level.leq (.succ l) .zero = some false := by
      unfold Ix.Kernel.Level.leq
      rw [show Ix.Kernel.Level.defaultFuel = 9998 + 1 + 1 from rfl]
      unfold Ix.Kernel.Level.leqCore
      have hlt0 : ¬ ((0 : Int) < 0) := by decide
      simp only [Ix.Kernel.Level.simplify, reduceCtorEq, false_and, ↓reduceIte, hlt0, and_false]
      unfold Ix.Kernel.Level.rest
      unfold Ix.Kernel.Level.leqCore
      have hge1 : ¬ ((0 - 1 : Int) ≥ 0) := by decide
      have hlt1 : (0 - 1 : Int) < 0 := by decide
      simp only [hge1, and_false, ↓reduceIte, eq_self, hlt1, and_self]
    unfold Ix.Kernel.Level.isEquiv
    have h1 : (Ix.Kernel.Level.succ l == .zero) = false :=
      beq_eq_false_iff_ne.mpr (by simp)
    simp only [h1, Bool.false_eq_true, ↓reduceIte, Ix.Kernel.Level.simplify, reduceCtorEq,
      hleq, bind, Option.bind, pure]
  | max _ _ | imax _ _ => cases h

private theorem checkSingleRecShape_sound {nPd indIndices : Nat}
    {tcv : CVal .anon} {tsh : ExprShape}
    (htsh : MatchesShape tcv.type tsh)
    {outC : List (CVal .anon × Nat × Nat)} {pairs : List (CName .anon × Nat)}
    (hpairs : outC.map (fun (cv, _, nF) => (cv.name, nF)) = pairs)
    {rcv : CVal .anon} {rc : RecCounts} {rules : List (Ix.Kernel.RecRule .anon)}
    (hchk : checkSingleRecShape nPd tsh pairs rc = true) :
    let rb : BlockRead .anon :=
      ⟨nPd, #[(tcv, nPd, indIndices)], outC.toArray, #[pairs.map Prod.fst], #[(rcv, rc, rules)]⟩
    Ix.Cert.LowerTransfer.Checks rb ∧
      Ix.Kernel.Frontend.InModel.wants (Ix.Cert.CtxAgree.blockRecOf rb) = false := by
  intro rb
  unfold checkSingleRecShape at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hpar, hmot⟩, hmin⟩, hkchk⟩, htele⟩ := hchk
  have hpar' : rc.params = nPd := beq_iff_eq.mp hpar
  have hmot' : rc.motives = 1 := beq_iff_eq.mp hmot
  have hlen_c : outC.length = pairs.length := by
    rw [← hpairs, List.length_map]
  have hmin' : rc.minors = outC.toArray.size := by
    rw [List.size_toArray, hlen_c]; exact beq_iff_eq.mp hmin
  have hnest : Ix.Cert.CtxAgree.numNestedOf rb = 0 := by
    simp [Ix.Cert.CtxAgree.numNestedOf, rb, hmot']
  have hwants : Ix.Kernel.Frontend.InModel.wants (Ix.Cert.CtxAgree.blockRecOf rb) = false := by
    unfold Ix.Kernel.Frontend.InModel.wants Ix.Cert.CtxAgree.blockRecOf
    rw [hnest]
    dsimp only [rb, List.toList_toArray]
    rfl
  refine ⟨⟨fun hn => absurd hnest hn, fun _ x hx => ?_⟩, hwants⟩
  dsimp only [rb] at hx
  rw [List.mem_singleton] at hx
  subst hx
  refine ⟨hpar', ?_, hmin', ?_, ?_⟩
  · dsimp only [rb]; rw [List.size_toArray]; exact hmot'
  · intro kE hkE
    unfold Ix.Cert.LowerTransfer.kExpectedOf at hkE
    dsimp only [rb, List.toList_toArray] at hkE
    unfold kCheckSingleShape at hkchk
    cases outC with
    | nil =>
      simp only [List.map_nil] at hpairs
      subst hpairs
      dsimp only at hkchk hkE
      injection hkE with hkE; subst hkE
      exact beq_iff_eq.mp hkchk
    | cons c0 tl =>
      rcases c0 with ⟨cv0, nP0, nF0⟩
      cases tl with
      | cons c1 tl' =>
        simp only [List.map_cons] at hpairs
        subst hpairs
        dsimp only at hkchk hkE
        injection hkE with hkE; subst hkE
        exact beq_iff_eq.mp hkchk
      | nil =>
        simp only [List.map_cons, List.map_nil] at hpairs
        subst hpairs
        simp only [List.map_cons, List.map_nil] at hkchk hkE
        obtain ⟨_, hsort_sh⟩ := htsh
        cases hps : tsh.piSort? with
        | none =>
          rw [hps] at hsort_sh
          dsimp only at hsort_sh
          cases hpr : tcv.type.piResult with
          | sort s => exact absurd hpr (hsort_sh.2 s)
          | _ => rw [hpr] at hkE; cases hkE
        | some s =>
          rw [hps] at hsort_sh hkchk
          dsimp only at hsort_sh hkchk
          rw [hsort_sh.1] at hkE
          dsimp only at hkE
          cases hnF : (nF0 == 0) with
          | false =>
            simp only [hnF, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at hkchk hkE
            injection hkE with hkE; subst hkE
            exact beq_iff_eq.mp hkchk
          | true =>
            simp only [hnF, ↓reduceIte, Bool.true_and] at hkchk hkE
            cases hlz : levelIsZeroFast s with
            | none => rw [hlz] at hkchk; cases hkchk
            | some b =>
              rw [hlz] at hkchk
              rw [levelIsZeroFast_sound hlz] at hkE
              have hbeq_b : (some b == some true) = b := by cases b <;> rfl
              rw [hbeq_b] at hkE
              injection hkE with hkE; subst hkE
              exact beq_iff_eq.mp hkchk
  · intro m ty p i n hm_eq hty_get hpi_len
    dsimp only [rb] at hty_get ⊢
    rw [List.getElem?_toArray] at hty_get
    cases m with
    | succ m' => cases hty_get
    | zero =>
      injection hty_get with hty_eq
      rcases Prod.mk.inj hty_eq with ⟨rfl, _⟩
      rw [hm_eq] at htele
      obtain ⟨_, hsort_sh⟩ := htsh
      cases hps : tsh.piSort? with
      | none =>
        rw [hps] at hsort_sh
        rw [hsort_sh.1] at hpi_len
        cases hpi_len
      | some s =>
        rw [hps] at hsort_sh htele
        dsimp only at hsort_sh htele
        rw [hsort_sh.2] at hpi_len
        injection hpi_len with hn_eq
        subst hn_eq
        exact beq_iff_eq.mp htele

include hev_defn in
private theorem pureReadInductive1Names_sound {owner : _root_.Address} {c : Ixon.Constant}
    {ind : Ixon.Inductive} {declNames : List (CName .anon)}
    (h : pureReadInductive1Names owner c ind = some declNames) (st : State .anon) :
    ∃ (r : Read .anon) (d : CDecl .anon),
      readInductive (defCx ev) st owner c #[.indc ind] = .ok r ∧
      r.decls = #[d] ∧
      d.names = declNames := by
  unfold pureReadInductive1Names at h
  dsimp only [bind, Option.bind] at h
  cases hsh : pureBlocksLookup owner with
  | none => rw [hsh] at h; cases h
  | some shPair =>
    rcases shPair with ⟨orderL, recsL⟩
    rw [hsh] at h
    dsimp only at h
    cases hord : (orderL == [0]) with
    | false => rw [hord] at h; cases h
    | true =>
      simp only [hord, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hord_eq : orderL = [0] := beq_iff_eq.mp hord
      subst hord_eq
      cases recsL with
      | nil => cases h
      | cons recRef recsTl =>
        cases recsTl with
        | cons _ _ => cases h
        | nil =>
          dsimp only at h
          cases hent : pureRecsLookup recRef with
          | none => rw [hent] at h; cases h
          | some entry =>
            rw [hent] at h
            dsimp only at h
            cases hu : ind.isUnsafe with
            | true => rw [hu] at h; cases h
            | false =>
              simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
              cases htk : pureMemberKeyOpt (.member owner 0) with
              | none => rw [htk] at h; cases h
              | some tk =>
                rw [htk] at h
                dsimp only at h
                let selfOk : Nat → Bool := fun i => i == 0
                cases htsh : pureReadExprShape c id selfOk ind.typ with
                | none => rw [htsh] at h; cases h
                | some tsh =>
                  rw [htsh] at h
                  dsimp only at h
                  rw [← Array.toList_zipIdx] at h
                  cases hpairs : pureReadCtorShapes owner c selfOk ind.params.toNat ind.ctors.zipIdx.toList with
                  | none => rw [hpairs] at h; cases h
                  | some pairs =>
                    rw [hpairs] at h
                    dsimp only at h
                    cases hrec : pureReadRecursorKeyCounts (List.range ind.lvls.toNat) recRef entry with
                    | none => rw [hrec] at h; cases h
                    | some recPair =>
                      rcases recPair with ⟨rkey, rc⟩
                      rw [hrec] at h
                      dsimp only at h
                      cases hchk : checkSingleRecShape ind.params.toNat tsh pairs rc with
                      | false => rw [hchk] at h; cases h
                      | true =>
                        simp only [hchk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
                        cases hnd : nodupNat (((tk :: pairs.map Prod.fst) ++ [rkey]).map cnameCode) with
                        | false => rw [hnd] at h; cases h
                        | true =>
                          simp only [hnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                            Option.some.injEq] at h
                          subst h
                          have hsh_cx := defCx_index_blocks_of_pure ev hev_defn hsh
                          have hent_cx := defCx_index_recs_of_pure ev hev_defn hent
                          have htk' := pureMemberKeyOpt_sound ev hev_defn htk
                          let rself := Ix.CompileCert.InductiveReading.blockSelf (defCx ev) owner #[.indc ind]
                          have hself : ∀ i, selfOk i = true → ∃ rm k, rself i = some rm ∧ rm = .ok k := by
                            intro i hso
                            dsimp only [selfOk] at hso
                            have hi0 : i = 0 := beq_iff_eq.mp hso
                            subst hi0
                            dsimp only [rself, Ix.CompileCert.InductiveReading.blockSelf]
                            exact ⟨_, tk, rfl, htk'⟩
                          let mrInd := MemberReader.mk' (defCx ev) c id rself
                          obtain ⟨tty, htty', htsh_m⟩ := pureReadExprShape_sound ev hev_defn hself htsh
                          obtain ⟨outC, hctors', hmap_c⟩ := pureReadCtorShapes_sound ev hev_defn hself
                            ind.ctors.zipIdx.toList #[] [] hpairs
                          obtain ⟨rtyp, rules, hrec'⟩ := pureReadRecursorKeyCounts_sound ev hev_defn hrec
                          let tcv : CVal .anon := ⟨tk, List.range ind.lvls.toNat, tty⟩
                          let rcv : CVal .anon := ⟨rkey, recLps entry.large (List.range ind.lvls.toNat), rtyp⟩
                          let rb : BlockRead .anon :=
                            ⟨ind.params.toNat, #[(tcv, ind.params.toNat, ind.indices.toNat)],
                              outC.toArray, #[pairs.map Prod.fst], #[(rcv, rc, rules)]⟩
                          obtain ⟨hChecks, hwants⟩ :=
                            checkSingleRecShape_sound (indIndices := ind.indices.toNat)
                              (tcv := tcv) (rcv := rcv) (rules := rules) htsh_m hmap_c hchk
                          let rOut : Read .anon :=
                            { decls := #[Ix.Cert.CtxAgree.indDeclOf rb],
                              owners := Ix.Cert.CtxAgree.ownersOf rb,
                              blocks := Ix.Cert.CtxAgree.blocksOf rb }
                          have hd_names : (Ix.Cert.CtxAgree.indDeclOf rb).names =
                              (tk :: pairs.map Prod.fst) ++ [rkey] := by
                            unfold Ix.Cert.CtxAgree.indDeclOf
                            dsimp only [rb, tcv, rcv, List.toList_toArray, Ix.Kernel.Declaration.names]
                            have hcnames : outC.map ((fun x => x.name) ∘ fun x => Ix.Kernel.ConstantInfo.ctorInfo x.1 x.2.1 x.2.2) =
                                pairs.map Prod.fst := by
                              rw [← hmap_c, List.map_map]
                              rfl
                            simp only [List.map_append, List.map_cons, List.map_nil, List.map_map]
                            rw [hcnames]
                            rfl
                          have hlow' : lowerInductive st rb = .ok rOut := by
                            rw [Ix.Cert.LowerTransfer.lowerInductive_iff]
                            refine ⟨hChecks, .inr ⟨hwants, rfl⟩, ?_⟩
                            simp only [rOut, List.toList_toArray, List.flatMap_cons,
                              List.flatMap_nil, List.append_nil, hd_names]
                            exact nodup_of_nodup_map cnameCode (nodup_of_nodupNat hnd)
                          have htypes_loop :=
                            Ix.CompileCert.InductiveReading.typeLoop (defCx ev) owner mrInd ind htk' htty'
                          have hctors_loop :
                              forIn (m := ReadM) (#[(0, ind)] : Array (Nat × Ixon.Inductive))
                                ((#[], #[]) : Array (CVal .anon × Nat × Nat) × Array (List (CName .anon)))
                                (Ix.CompileCert.InductiveReading.ctorClassStep (defCx ev) owner mrInd ind.params.toNat) =
                              .ok (outC.toArray, #[pairs.map Prod.fst]) := by
                            rw [← Array.forIn_toList, List.forIn_cons]
                            have hcstep : Ix.CompileCert.InductiveReading.ctorClassStep (defCx ev) owner mrInd
                                ind.params.toNat (0, ind) (#[], #[]) =
                                .ok (.yield (outC.toArray, #[pairs.map Prod.fst])) := by
                              unfold Ix.CompileCert.InductiveReading.ctorClassStep
                              dsimp only
                              rw [← Array.forIn_toList, hctors']
                              simp only [bind, Except.bind, pure, Except.pure,
                                Array.empty_append, List.nil_append]
                              rfl
                            rw [hcstep]
                            dsimp only [bind, Except.bind]
                            rw [List.forIn_nil]
                            rfl
                          have hrecs_loop :
                              Ix.CompileCert.InductiveReading.readRecursors (defCx ev)
                                (List.range ind.lvls.toNat) #[recRef] = .ok #[(rcv, rc, rules)] := by
                            unfold Ix.CompileCert.InductiveReading.readRecursors
                            rw [← Array.forIn_toList, List.forIn_cons]
                            have hrstep : Ix.CompileCert.InductiveReading.recursorStep (defCx ev)
                                (List.range ind.lvls.toNat) recRef #[] = .ok (.yield #[(rcv, rc, rules)]) := by
                              unfold Ix.CompileCert.InductiveReading.recursorStep
                              rw [hent_cx]
                              dsimp only
                              rw [hrec']
                              rfl
                            rw [hrstep]
                            dsimp only [bind, Except.bind]
                            rw [List.forIn_nil]
                            rfl
                          have hshaped : blockShapeOf (defCx ev).index owner #[.indc ind] =
                              some ⟨#[0], #[recRef]⟩ := by
                            simp only [blockShapeOf, hsh_cx]
                          dsimp only [mrInd, rself] at htypes_loop hctors_loop
                          refine ⟨rOut, Ix.Cert.CtxAgree.indDeclOf rb, ?_, rfl, hd_names⟩
                          rw [Ix.CompileCert.InductiveReading.readInductive_eq]
                          unfold Ix.CompileCert.InductiveReading.readInductiveSpec
                          rw [hshaped]
                          dsimp only
                          rw [Ix.CompileCert.InductiveReading.indcs_singleton]
                          simp only [List.size_toArray, List.length_cons, List.length_nil,
                            Nat.zero_add, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
                            List.getElem?_toArray, List.getElem?_cons_zero, List.any_toArray',
                            List.all_toArray', List.any_cons, List.any_nil, List.all_cons,
                            List.all_nil, hu, Bool.or_false, Bool.and_true, htypes_loop,
                            hctors_loop, hrecs_loop, bind, Except.bind, pure, Except.pure]
                          exact hlow'

include hev_defn in
private theorem pureReadRecordNames_sound {owner : _root_.Address} {c : Ixon.Constant}
    (hc : (owner, c) ∈ committedPreludeList) {groups : List (List (CName .anon))}
    (h : pureReadRecordNames owner c = some groups) (st : State .anon) :
    ∃ (r : Read .anon),
      readRecord (defCx ev) st owner c = .ok r ∧
      r.decls.toList.map Ix.Kernel.Declaration.names = groups := by
  unfold pureReadRecordNames at h
  have hself_none : ∀ (i : Nat), (fun _ : Nat => false) i = true →
      ∃ rm k, (fun _ : Nat => (none : Option (ReadM (CName .anon)))) i = some rm ∧ rm = .ok k :=
    fun _ hf => nomatch hf
  cases hci : c.info with
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    rw [hci] at h
    dsimp only at h
    cases hnone : (resolveSource preStorePure owner c).isNone with
    | true => rw [hnone] at h; cases h
    | false =>
      simp only [hnone, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨{}, ?_, rfl⟩
      unfold readRecord
      rw [hci]
      dsimp only
      rw [resolveSource_defCx_eq_pure ev hc, hnone]
      simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
  | recr rc =>
    rw [hci] at h
    dsimp only at h
    cases hp : pureRecsLookup (.member owner 0) with
    | none => rw [hp] at h; cases h
    | some entry =>
      simp only [hp, Option.isSome_some, ↓reduceIte, Option.some.injEq] at h
      subst h
      have hcx_rec := defCx_index_recs_of_pure ev hev_defn hp
      have hcont : (defCx ev).index.recs.contains (.member owner 0) = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, hcx_rec]; rfl
      refine ⟨{}, ?_, rfl⟩
      unfold readRecord
      rw [hci]
      dsimp only
      simp only [hcont, ↓reduceIte, pure, Except.pure]
  | axio a =>
    rw [hci] at h
    dsimp only [bind, Option.bind] at h
    cases hu : a.isUnsafe with
    | true => rw [hu] at h; cases h
    | false =>
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      cases hck : pureMemberKeyOpt (.member owner 0) with
      | none => rw [hck] at h; cases h
      | some ck =>
        rw [hck] at h
        dsimp only at h
        cases hty : pureReadExprShape c id (fun _ => false) a.typ with
        | none => rw [hty] at h; cases h
        | some tsh =>
          rw [hty] at h
          injection h with hg; subst hg
          have hck' := pureMemberKeyOpt_sound ev hev_defn hck
          obtain ⟨ty, hty', -⟩ := pureReadExprShape_sound ev hev_defn hself_none hty
          refine ⟨{ decls := #[.axiomDecl ⟨ck, List.range a.lvls.toNat, ty⟩] }, ?_, rfl⟩
          unfold readRecord
          rw [hci]
          dsimp only
          simp only [hu, Bool.false_eq_true, ↓reduceIte, hck', hty',
            bind, Except.bind, pure, Except.pure]
  | quot q =>
    rw [hci] at h
    dsimp only [bind, Option.bind] at h
    cases hck : pureMemberKeyOpt (.member owner 0) with
    | none => rw [hck] at h; cases h
    | some ck =>
      rw [hck] at h
      dsimp only at h
      cases hty : pureReadExprShape c id (fun _ => false) q.typ with
      | none => rw [hty] at h; cases h
      | some tsh =>
        rw [hty] at h
        injection h with hg; subst hg
        have hck' := pureMemberKeyOpt_sound ev hev_defn hck
        obtain ⟨ty, hty', -⟩ := pureReadExprShape_sound ev hev_defn hself_none hty
        let kind : Ix.Kernel.QuotKind := match q.kind with
          | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind
        refine ⟨{ decls := #[.quotDecl kind ⟨ck, List.range q.lvls.toNat, ty⟩] }, ?_, rfl⟩
        unfold readRecord
        rw [hci]
        dsimp only
        simp only [hck', hty', bind, Except.bind, pure, Except.pure]
        rfl
  | muts ms =>
    rw [hci] at h
    dsimp only [bind, Option.bind] at h
    cases hms : ms.toList with
    | nil => rw [hms] at h; cases h
    | cons m0 tl =>
      cases m0 with
      | defn _ | recr _ => rw [hms] at h; cases h
      | indc ind =>
        cases tl with
        | cons _ _ => rw [hms] at h; cases h
        | nil =>
          rw [hms] at h
          dsimp only at h
          cases hind : pureReadInductive1Names owner c ind with
          | none => rw [hind] at h; cases h
          | some dnames =>
            rw [hind] at h
            injection h with hg; subst hg
            have harr : ms = #[.indc ind] := Array.ext' hms
            subst harr
            obtain ⟨r, d, hr, hr_decls, hd_names⟩ :=
              pureReadInductive1Names_sound ev hev_defn hind st
            refine ⟨r, ?_, ?_⟩
            · rw [Ix.CompileCert.InductiveReading.readRecord_inductive (defCx ev) st owner c ind hci]
              exact hr
            · rw [hr_decls, List.toList_toArray, List.map_cons, List.map_nil, hd_names]
  | defn _ => rw [hci] at h; cases h

include hev_defn in
private theorem pureReadStreamNames_sound :
    ∀ (rs : List (_root_.Address × Ixon.Constant)) {groups : List (List (CName .anon))},
      (∀ p ∈ rs, p ∈ committedPreludeList) →
      pureReadStreamNames rs = some groups →
      ∀ st : State .anon,
        ∃ (st' : State .anon) (decls : List (CDecl .anon)),
          StreamRead (defCx ev) st rs st' decls.toArray ∧
          decls.map Ix.Kernel.Declaration.names = groups
  | [], _, _, h, st => by
    unfold pureReadStreamNames at h
    injection h with hg; subst hg
    exact ⟨st, [], .nil, rfl⟩
  | (a, c) :: rest, _, hsub, h, st => by
    unfold pureReadStreamNames at h
    dsimp only [bind, Option.bind] at h
    cases hg1 : pureReadRecordNames a c with
    | none => rw [hg1] at h; cases h
    | some g1 =>
      rw [hg1] at h
      dsimp only at h
      cases hgs : pureReadStreamNames rest with
      | none => rw [hgs] at h; cases h
      | some gs =>
        rw [hgs] at h
        injection h with htot; subst htot
        obtain ⟨r, hr, hr_names⟩ :=
          pureReadRecordNames_sound ev hev_defn (hsub (a, c) List.mem_cons_self) hg1 st
        obtain ⟨st', tailDecls, hst', htail_names⟩ := pureReadStreamNames_sound rest
          (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) hgs (st.commit r)
        refine ⟨st', r.decls.toList ++ tailDecls, ?_, ?_⟩
        · have happ : (r.decls.toList ++ tailDecls).toArray = r.decls ++ tailDecls.toArray := by
            apply Array.ext'; simp
          rw [happ]
          exact .cons hr hst'
        · rw [List.map_append, hr_names, htail_names]

end WithEv

private theorem fallbackRecursorShapeFast_eq (c : Ixon.Constant) :
    fallbackRecursorShapeFast c = fallbackRecursorShape c := by
  unfold fallbackRecursorShapeFast fallbackRecursorShape
  cases c.info with
  | muts ms => dsimp only; rw [← Array.all_toList]; rfl
  | _ => rfl

private theorem eqRoleGroup_sound :
    ∀ (ks : List (CName .anon)) (rs : List Ix.Kernel.Role),
      eqRoleGroup ks rs = true →
      ks = rs.map (Ix.Kernel.Key.role (md := .anon))
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | .id _ :: _, _, h => by cases h
  | .aux _ _ :: _, _, h => by cases h
  | .role _ :: _, [], h => by cases h
  | .role r1 :: ks, r2 :: rs, h => by
    unfold eqRoleGroup at h
    rw [Bool.and_eq_true, beq_iff_eq] at h
    rw [Ix.Kernel.Role.idx_inj h.1, eqRoleGroup_sound ks rs h.2, List.map_cons]

private theorem eqRoleGroups_sound :
    ∀ (gs : List (List (CName .anon))) (rs : List (List Ix.Kernel.Role)),
      eqRoleGroups gs rs = true →
      gs = rs.map (·.map (Ix.Kernel.Key.role (md := .anon)))
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | g :: gs, r :: rs, h => by
    unfold eqRoleGroups at h
    rw [Bool.and_eq_true] at h
    rw [eqRoleGroup_sound g r h.1, eqRoleGroups_sound gs rs h.2, List.map_cons]

/-- The committed prelude succeeds under `committedDefaultRoleTable` in `.anon` mode. -/
theorem preludeFor_defaultRoleTable :
    ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) committedDefaultRoleTable = .ok pre := by
  have hchk := purePreludeCheck_ok
  unfold purePreludeCheckBool at hchk
  cases hps : pureReadStreamNames committedPreludeList with
  | none => rw [hps] at hchk; cases hchk
  | some groups =>
    rw [hps, Bool.and_eq_true] at hchk
    obtain ⟨hshape_bool, hrec_pre⟩ := hchk
    have hgroups_eq := eqRoleGroups_sound groups Ix.Kernel.preludeShape hshape_bool
    obtain ⟨ev, hev_eq, -, hev_defn⟩ := evidenceRecords_spec
    obtain ⟨st', decls, hstream, hdecls_names⟩ :=
      pureReadStreamNames_sound ev hev_defn committedPreludeList (fun _ h => h) hps {}
    have hrr := Ix.Cert.Stream.readRecords_complete hstream committedPreAddrs_nodup
    have hrr' : readRecords (defCx ev) {} committedPrelude = .ok (st', decls.toArray) := hrr
    have hread : preludeRead (md := .anon) committedDefaultRoleTable =
        .ok ⟨committedPrelude, ev, committedBlobs, ⟨decls.toArray⟩, st'⟩ := by
      unfold preludeRead
      rw [preludeRecords_eq, hev_eq, evidenceBlobs_eq]
      simp only [bind, Except.bind, readPrelude_defCx_eq ev, hrr']
    have hshape_beq :
        (decls.map (·.names) ==
          Ix.Kernel.preludeShape.map (·.map (Ix.Kernel.Key.role (md := .anon)))) = true :=
      beq_iff_eq.mpr (hdecls_names.trans hgroups_eq)
    have hcs : checkPreludeShape (md := .anon)
        ⟨committedPrelude, ev, committedBlobs, ⟨decls.toArray⟩, st'⟩ = .ok () := by
      unfold checkPreludeShape
      simp only [List.toList_toArray, hshape_beq, ↓reduceIte, pure, Except.pure]
    have hcfr : checkFallbackRecursors (md := .anon)
        ⟨committedPrelude, ev, committedBlobs, ⟨decls.toArray⟩, st'⟩ = .ok () := by
      unfold checkFallbackRecursors
      have hall : (committedPrelude ++ ev).all (fun p => fallbackRecursorShape p.2) = true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro p hp
        rcases Array.mem_append.mp hp with h1 | h2
        · have hp' : p ∈ committedPreludeList := Array.mem_toList_iff.mpr h1
          rw [← fallbackRecursorShapeFast_eq]
          exact List.all_eq_true.mp hrec_pre p hp'
        · obtain ⟨d, hd⟩ := hev_defn p (Array.mem_toList_iff.mpr h2)
          simp [fallbackRecursorShape, hd]
      simp only [hall, ↓reduceIte, pure, Except.pure]
    refine ⟨⟨committedPrelude, ev, committedBlobs, ⟨decls.toArray⟩, st'⟩, ?_⟩
    unfold preludeFor
    rw [hread]
    simp only [bind, Except.bind, pure, Except.pure, hcs, hcfr]

/-! ## `ReaderTable` and `TableAdmitted` consequences: `preludeFor` and `LiteralSupportBound` -/

/-- Under `TableAdmitted V b` and `admitBinding Address.admissionHash b = .ok t`,
`preludeFor (md := .anon) t` succeeds. -/
theorem preludeFor_of_tableAdmitted {V : View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable}
    (htab : IxVM.Refinement.TableAdmitted V b)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) t = .ok pre := by
  obtain ⟨t', hadm', _, hacc⟩ := htab
  rw [hadm] at hadm'
  injection hadm' with ht_eq
  subst ht_eq
  obtain ⟨_, _, _, _, -, -, t'', pre, _, _, hadm'', -, -, hpre, -⟩ := hacc
  dsimp only [IxVM.Refinement.Scope.strict] at hadm''
  rw [hadm] at hadm''
  injection hadm'' with ht_eq'
  subst ht_eq'
  exact ⟨pre, hpre⟩

/-- Under `TableAdmitted V b` and `admitBinding Address.admissionHash b = .ok t`,
`LiteralSupportBound t` holds. -/
theorem literalSupportBound_of_tableAdmitted {V : View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable}
    (htab : IxVM.Refinement.TableAdmitted V b)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    IxVM.Refinement.LiteralSupportBound t := by
  obtain ⟨t', hadm', hlit, _⟩ := htab
  rw [hadm] at hadm'
  injection hadm' with ht_eq
  subst ht_eq
  exact hlit

/-- Under `ReaderTable clm V b` and `admitBinding Address.admissionHash b = .ok t`,
`preludeFor (md := .anon) t` succeeds. -/
theorem preludeFor_of_readerTable {clm : Ix.Claim} {V : View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable}
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) t = .ok pre :=
  preludeFor_of_tableAdmitted hrt.tableAdmitted hadm

/-- Under `ReaderTable clm V b` and `admitBinding Address.admissionHash b = .ok t`,
`LiteralSupportBound t` holds. -/
theorem literalSupportBound_of_readerTable {clm : Ix.Claim} {V : View}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    IxVM.Refinement.LiteralSupportBound t :=
  literalSupportBound_of_tableAdmitted hrt.tableAdmitted hadm

/-! ## Collision-free agreement between `committedImages` / `pre` fallback and `LoadedBy calls E₀` -/

private theorem except_bind_ok_inv {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem serConstant_mem_committedImages_of_fallback {md : Ix.Kernel.Mode}
    {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre) {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence) :
    Ixon.serConstant c ∈ IxVM.Consistency.committedImages ∧
      Address.blake3Pure (Ixon.serConstant c) = a ∧
      c.wireWF := by
  obtain ⟨hauth, hwf⟩ := Ix.Cert.FallbackStore.fallback_authentic fallbackHashed hpre hmem
  have hblake : Address.blake3Pure (Ixon.serConstant c) = a := by
    rw [← Address.admissionHash_eq]
    exact hauth.symm
  obtain ⟨hrec, hev⟩ := Ix.Cert.ReaderFallback.preludeFor_records hpre
  have hrow : ∃ row ∈ (RoleData.prelude ++ RoleData.evidence).toList,
      ∃ b, bytesOfHex row.2 = some b ∧
        Ixon.Canonical.deConstant preludeMaxBytes preludeMaxUnivNodes b = .ok c := by
    rcases Array.mem_append.mp hmem with h1 | h2
    · obtain ⟨row, hr, _, b, hb, hdc⟩ :=
        Ix.Cert.FallbackStore.decoded_rows "prelude" RoleData.prelude hrec (a, c)
          (Array.mem_toList_iff.mpr h1)
      exact ⟨row, by simp [Array.toList_append, hr], b, hb, hdc⟩
    · obtain ⟨row, hr, _, b, hb, hdc⟩ :=
        Ix.Cert.FallbackStore.decoded_rows "evidence" RoleData.evidence hev (a, c)
          (Array.mem_toList_iff.mpr h2)
      exact ⟨row, by simp [Array.toList_append, hr], b, hb, hdc⟩
  obtain ⟨row, hr, b, hb, hdc⟩ := hrow
  have hser : Ixon.serConstant c = b := (Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hdc).2.2
  refine ⟨?_, hblake, hwf⟩
  unfold IxVM.Consistency.committedImages
  rw [List.mem_filterMap]
  refine ⟨row.2, ?_, ?_⟩
  · rw [List.mem_map]
    refine ⟨row, ?_, rfl⟩
    rw [Array.toList_append]
    exact List.mem_append_left _ hr
  · rw [hser]; exact hb

private theorem preludeFor_blobs {md : Ix.Kernel.Mode} {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre) :
    evidenceBlobs = .ok pre.blobs := by
  unfold preludeFor at hpre
  obtain ⟨pre₀, hread, hrest⟩ := except_bind_ok_inv hpre
  obtain ⟨_, _, hrest'⟩ := except_bind_ok_inv hrest
  obtain ⟨_, _, hpure⟩ := except_bind_ok_inv hrest'
  injection hpure with heq; subst heq
  unfold preludeRead at hread
  obtain ⟨recs, _, hr1⟩ := except_bind_ok_inv hread
  obtain ⟨evs, _, hr2⟩ := except_bind_ok_inv hr1
  obtain ⟨blobs, hblobs, hr3⟩ := except_bind_ok_inv hr2
  unfold readPrelude at hr3
  dsimp only at hr3
  cases hrr : readRecords (contextOf t recs [] evs blobs) {} recs with
  | error err => rcases err with ⟨_, _⟩; rw [hrr] at hr3; cases hr3
  | ok pair =>
    rcases pair with ⟨_, _⟩
    rw [hrr] at hr3
    injection hr3 with hp
    cases hp
    exact hblobs

theorem blob_mem_committedImages_of_fallback {md : Ix.Kernel.Mode}
    {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre) {a : _root_.Address} {blob : ByteArray}
    (hmem : (a, blob) ∈ pre.blobs) :
    blob ∈ IxVM.Consistency.committedImages ∧ Address.blake3Pure blob = a := by
  have heb := preludeFor_blobs hpre
  unfold evidenceBlobs at heb
  obtain ⟨⟨hex, bytes⟩, hrow, hrow_ok⟩ := except_mapM_rows heb (a, blob) hmem
  dsimp only at hrow_ok
  have ⟨ha, hb⟩ : addressOfHex hex = some a ∧ bytesOfHex bytes = some blob := by
    cases ha : addressOfHex hex with
    | none => rw [ha] at hrow_ok; cases hrow_ok
    | some a' =>
      rw [ha] at hrow_ok
      dsimp only at hrow_ok
      cases hb : bytesOfHex bytes with
      | none => rw [hb] at hrow_ok; cases hrow_ok
      | some b' =>
        rw [hb] at hrow_ok
        injection hrow_ok with hpair
        cases hpair
        exact ⟨rfl, rfl⟩
  have hhash := blobsHashed (hex, bytes) hrow
  rw [hb, ha, Option.map_some, Option.some.injEq, Address.admissionHash_eq] at hhash
  refine ⟨?_, hhash⟩
  unfold IxVM.Consistency.committedImages
  rw [List.mem_filterMap]
  refine ⟨bytes, ?_, hb⟩
  rw [List.mem_map]
  refine ⟨(hex, bytes), ?_, rfl⟩
  rw [Array.toList_append]
  exact List.mem_append_right _ hrow

/-- General collision-free agreement for any committed image: either `V.HashedCollision extra calls`
holds, or every byte string hashed in `calls` with the same pure BLAKE3 digest equals it. -/
theorem committedImages_agree_of_hashed {V : View} {extra : List ByteArray}
    {calls : List (Call IxVM.F)}
    (hsub : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    {img bytes : ByteArray} (himg : img ∈ IxVM.Consistency.committedImages)
    (hhashed : Hashed calls bytes)
    (heq_hash : Address.blake3Pure bytes = Address.blake3Pure img) :
    V.HashedCollision extra calls ∨ bytes = img := by
  by_cases hsame : bytes = img
  · exact .inr hsame
  · exact .inl (.inl ⟨Address.blake3Pure img, img, bytes,
      .inr (.inl ⟨hsub img himg, rfl⟩), hhashed, hsame, heq_hash⟩)

/-- Collision-free agreement between `pre.records ++ pre.evidence` and any `E₀` satisfying
`LoadedBy calls E₀`: either `V.HashedCollision extra calls`, or `lc.rawBytes = Ixon.serConstant c`. -/
theorem fallback_record_agree_of_loadedBy {md : Ix.Kernel.Mode}
    {V : View} {extra : List ByteArray} {calls : List (Call IxVM.F)} {E₀ : Ixon.Env}
    (hsub : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    {t : Ix.Kernel.RoleTable} {pre : Prelude md} (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant} (hmem : (a, c) ∈ pre.records ++ pre.evidence)
    {lc : Ixon.LazyConstant} (hget : E₀.consts.get? a = some lc) :
    V.HashedCollision extra calls ∨ (lc.rawBytes = Ixon.serConstant c ∧ c.wireWF) := by
  obtain ⟨himg, hblake, hwf⟩ := serConstant_mem_committedImages_of_fallback hpre hmem
  obtain ⟨hhashed, hlc_blake⟩ := hload.1 a lc hget
  rcases committedImages_agree_of_hashed hsub himg hhashed (hlc_blake.trans hblake.symm) with
    hcol | hraw
  · exact .inl hcol
  · exact .inr ⟨hraw, hwf⟩

/-- When `E₀` also satisfies `L1.EnvDecoded E₀`, any record at `a` in `E₀` decodes to the
committed fallback constant `c` (`Ix.Cert.recordAt E₀ a = some c`), unless `HashedCollision`. -/
theorem fallback_recordAt_of_loadedBy {md : Ix.Kernel.Mode}
    {V : View} {extra : List ByteArray} {calls : List (Call IxVM.F)} {E₀ : Ixon.Env}
    (hsub : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hdec : L1.EnvDecoded E₀)
    {t : Ix.Kernel.RoleTable} {pre : Prelude md} (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant} (hmem : (a, c) ∈ pre.records ++ pre.evidence)
    {lc : Ixon.LazyConstant} (hget : E₀.consts.get? a = some lc) :
    V.HashedCollision extra calls ∨ Ix.Cert.recordAt E₀ a = some c := by
  rcases fallback_record_agree_of_loadedBy hsub hload hpre hmem hget with hcol | ⟨hraw, hwf⟩
  · exact .inl hcol
  · right
    obtain ⟨c', hget_c', hexact⟩ := hdec a lc hget
    rw [hraw, Ixon.Verify.deConstantExact_serConstant c hwf] at hexact
    injection hexact with hce
    subst hce
    unfold Ix.Cert.recordAt
    rw [hget]
    exact hget_c'

/-- Collision-free agreement between `pre.blobs` and `E₀.blobs` under `LoadedBy calls E₀`. -/
theorem fallback_blob_agree_of_loadedBy {md : Ix.Kernel.Mode}
    {V : View} {extra : List ByteArray} {calls : List (Call IxVM.F)} {E₀ : Ixon.Env}
    (hsub : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    {t : Ix.Kernel.RoleTable} {pre : Prelude md} (hpre : preludeFor t = .ok pre)
    {a : _root_.Address} {blob raw : ByteArray} (hmem : (a, blob) ∈ pre.blobs)
    (hget : E₀.blobs.get? a = some raw) :
    V.HashedCollision extra calls ∨ raw = blob := by
  obtain ⟨himg, hblake⟩ := blob_mem_committedImages_of_fallback hpre hmem
  obtain ⟨hhashed, hraw_blake⟩ := hload.2 a raw hget
  exact committedImages_agree_of_hashed hsub himg hhashed (hraw_blake.trans hblake.symm)

/-- Bundled agreement between `pre`'s fallback records/blobs and `E₀` for the exact
`ConsistencySpec` extra-images list `claimBytes :: b.bytes :: committedImages`. -/
theorem committedImages_agree_of_loadedBy {md : Ix.Kernel.Mode}
    {V : View} {claimBytes : ByteArray} {b : Ix.Kernel.Admission.Binding}
    {calls : List (Call IxVM.F)} {E₀ : Ixon.Env}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    {t : Ix.Kernel.RoleTable} {pre : Prelude md} (hpre : preludeFor t = .ok pre) :
    V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.committedImages) calls ∨
      ((∀ a c lc, (a, c) ∈ pre.records ++ pre.evidence → E₀.consts.get? a = some lc →
          lc.rawBytes = Ixon.serConstant c ∧ c.wireWF) ∧
       (∀ a blob raw, (a, blob) ∈ pre.blobs → E₀.blobs.get? a = some raw → raw = blob)) := by
  have hsub : ∀ img ∈ IxVM.Consistency.committedImages,
      img ∈ claimBytes :: b.bytes :: IxVM.Consistency.committedImages :=
    fun img hm => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  by_cases hcol : V.HashedCollision (claimBytes :: b.bytes :: IxVM.Consistency.committedImages) calls
  · exact .inl hcol
  · right
    refine ⟨?_, ?_⟩
    · intro a c lc hmem hget
      rcases fallback_record_agree_of_loadedBy hsub hload hpre hmem hget with hc | hok
      · exact absurd hc hcol
      · exact hok
    · intro a blob raw hmem hget
      rcases fallback_blob_agree_of_loadedBy hsub hload hpre hmem hget with hc | hok
      · exact absurd hc hcol
      · exact hok

end IxVM.Refinement.RoleVal
