import Ix.Cert.FallbackStore
import Ix.Cert.LowerDistinct
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.ReaderFallback
import Ix.Cert.ReadingKeys
import Ix.Cert.Stream
import Ix.CompileCert.ReaderIndex
import Ix.IxVM.Consistency.Statement
import IxVMRefinement.L1.Decode
import IxVMRefinement.RoleVal.CommittedData

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

set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

namespace IxVM.Refinement.RoleVal

open Ix.Kernel (ConstRef CName CVal CLevel CExpr CInfo CDecl)
open Ix.Kernel.Reader

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Pure store, role bindings, and recursor index on `committedDefaultRoleTable` -/

def committedPreAddrs : List _root_.Address :=
  committedPreludeList.map Prod.fst

private def preStorePure (a : _root_.Address) : Option Ixon.Constant :=
  committedPreludeList.lookup a

private def constRefBlock : ConstRef _root_.Address → _root_.Address
  | .member b _ => b
  | .ctor b _ _ => b

private def constRefCode : ConstRef _root_.Address → Nat
  | .member b i => addrHead32 b * 256 + i * 2
  | .ctor b i j => addrHead32 b * 256 + (i * 16 + j) * 2 + 1

private def cnameCode : CName .anon → Nat
  | .role r => r.toNat + 1
  | _ => 0

private theorem committedPreEvAddrs_nodup :
    (committedPreAddrs ++ committedEvAddrs).Nodup := by
  apply nodup_of_nodup_map addrHead32
  exact nodup_of_nodupNat (by decide +kernel)

private theorem committedPreAddrs_nodup : committedPreAddrs.Nodup :=
  (List.nodup_append.mp committedPreEvAddrs_nodup).1

private theorem preEvAddrs_disjoint {a : _root_.Address}
    (hp : a ∈ committedPreAddrs) (he : a ∈ committedEvAddrs) : False :=
  (List.nodup_append.mp committedPreEvAddrs_nodup).2.2 a hp a he rfl

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

private theorem lookup_eq_some_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α]
    {l : List (α × β)} (hnd : (l.map Prod.fst).Nodup) {k : α} {v : β}
    (hm : (k, v) ∈ l) : l.lookup k = some v := by
  induction l with
  | nil => cases hm
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    rcases List.mem_cons.mp hm with rfl | htl
    · simp
    · have hne : (k == hd.1) = false :=
        Bool.eq_false_iff.mpr fun hc =>
          hnd.1 (by rw [← beq_iff_eq.mp hc]; exact List.mem_map_of_mem htl)
      rw [hne]
      exact ih hnd.2 htl

private def preRefsAndProjClosedBool : Bool :=
  committedPreludeList.all fun (_, c) =>
    c.refs.toList.all committedPreAddrs.contains &&
    match c.info with
    | .cPrj p => committedPreAddrs.contains p.block
    | .rPrj p => committedPreAddrs.contains p.block
    | .iPrj p => committedPreAddrs.contains p.block
    | .dPrj p => committedPreAddrs.contains p.block
    | _ => true

private theorem preRefsAndProjClosed : preRefsAndProjClosedBool = true := by
  decide +kernel

private theorem pre_refs_mem {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ committedPreludeList) {r : _root_.Address} (hr : r ∈ c.refs.toList) :
    r ∈ committedPreAddrs := by
  have hall := List.all_eq_true.mp preRefsAndProjClosed (a, c) hc
  rw [Bool.and_eq_true, List.all_eq_true] at hall
  simpa [List.contains_iff_mem] using hall.1 r hr

private theorem pre_proj_block_mem {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ committedPreludeList) :
    (∀ p, c.info = .cPrj p → p.block ∈ committedPreAddrs) ∧
    (∀ p, c.info = .rPrj p → p.block ∈ committedPreAddrs) ∧
    (∀ p, c.info = .iPrj p → p.block ∈ committedPreAddrs) ∧
    (∀ p, c.info = .dPrj p → p.block ∈ committedPreAddrs) := by
  have hall := (Bool.and_eq_true.mp (List.all_eq_true.mp preRefsAndProjClosed (a, c) hc)).2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro p hp; rw [hp] at hall; simpa [List.contains_iff_mem] using hall)

section WithEv

variable (ev : Array (_root_.Address × Ixon.Constant))
  (hev_addrs : ev.toList.map Prod.fst = committedEvAddrs)
  (hev_defn : ∀ p ∈ ev.toList, ∃ d, p.2.info = .defn d)

private abbrev defCx : Ctx .anon :=
  contextOf committedDefaultRoleTable committedPrelude [] ev committedBlobs

private theorem defCx_store_of_mem_pre {a : _root_.Address} (ha : a ∈ committedPreAddrs) :
    (defCx ev).store a = preStorePure a := by
  show (recordMap committedPrelude)[a]? <|> ((recordMap ev)[a]? <|> none) =
    committedPreludeList.lookup a
  rw [Ix.Cert.ReaderClosureKeys.recordMap_get, show committedPrelude.toList = committedPreludeList from rfl]
  have hs := lookup_isSome_of_mem_map_fst ha
  cases hl : committedPreludeList.lookup a with
  | none => rw [hl] at hs; cases hs
  | some c => rfl

private theorem resolveSource_defCx_eq_pure {a : _root_.Address} {c : Ixon.Constant}
    (hc : (a, c) ∈ committedPreludeList) :
    resolveSource (defCx ev).store a c = resolveSource preStorePure a c := by
  have hblk := pre_proj_block_mem hc
  unfold resolveSource
  cases hci : c.info with
  | defn _ | recr _ | axio _ | quot _ | muts _ => rfl
  | cPrj p => rw [defCx_store_of_mem_pre ev (hblk.1 p hci)]
  | rPrj p => rw [defCx_store_of_mem_pre ev (hblk.2.1 p hci)]
  | iPrj p => rw [defCx_store_of_mem_pre ev (hblk.2.2.1 p hci)]
  | dPrj p => rw [defCx_store_of_mem_pre ev (hblk.2.2.2 p hci)]

private theorem resolve_defCx_of_mem_pre {a : _root_.Address} (ha : a ∈ committedPreAddrs) :
    resolve (defCx ev).store a = resolve preStorePure a := by
  unfold resolve
  rw [defCx_store_of_mem_pre ev ha]
  cases hl : preStorePure a with
  | none => rfl
  | some c =>
    simp only [bind, Option.bind]
    exact resolveSource_defCx_eq_pure ev (mem_of_lookup_eq_some hl)

private theorem resolve_defCx_not_mem_pre {a : _root_.Address}
    (ha : a ∉ committedPreAddrs) {ref : ConstRef _root_.Address}
    (hres : resolve (defCx ev).store a = some ref) :
    constRefBlock ref ∉ committedPreAddrs := by
  unfold resolve at hres
  have hpre_none : (recordMap committedPrelude)[a]? = none := by
    rw [Ix.Cert.ReaderClosureKeys.recordMap_get, show committedPrelude.toList = committedPreludeList from rfl]
    exact lookup_eq_none_of_not_mem_map_fst ha
  have hst : (defCx ev).store a = ev.toList.lookup a := by
    show (recordMap committedPrelude)[a]? <|> ((recordMap ev)[a]? <|> none) = _
    rw [hpre_none, Ix.Cert.ReaderClosureKeys.recordMap_get]
    cases ev.toList.lookup a <;> rfl
  rw [hst] at hres
  cases hel : ev.toList.lookup a with
  | none => rw [hel] at hres; cases hres
  | some c =>
    rw [hel] at hres
    obtain ⟨d, hd⟩ := hev_defn (a, c) (mem_of_lookup_eq_some hel)
    simp only [bind, Option.bind, resolveSource, hd, Option.some.injEq] at hres
    subst hres
    exact ha

/-! ### Pure role bindings -/

private def pureRolesList : List (ConstRef _root_.Address × CName .anon) :=
  committedDefaultRoleTable.bound.toList.filterMap fun (ro, a) =>
    if committedPreAddrs.contains a then
      (resolve preStorePure a).map fun ref => (ref, Ix.Kernel.roleKey ro)
    else none

private def pureRolesLookup (ref : ConstRef _root_.Address) : Option (CName .anon) :=
  pureRolesList.lookup ref

private theorem pureRolesList_nodup : (pureRolesList.map Prod.fst).Nodup := by
  apply nodup_of_nodup_map constRefCode
  exact nodup_of_nodupNat (by decide +kernel)

private theorem pureRolesList_block_mem :
    ∀ p ∈ pureRolesList, constRefBlock p.1 ∈ committedPreAddrs := by
  have hb : (pureRolesList.all fun p => committedPreAddrs.contains (constRefBlock p.1)) = true := by
    decide +kernel
  intro p hp
  simpa [List.contains_iff_mem] using List.all_eq_true.mp hb p hp

private def bindingsStep (store : Store) (m : Std.HashMap (ConstRef _root_.Address) (CName .anon))
    (p : Ix.Kernel.Role × _root_.Address) : Std.HashMap (ConstRef _root_.Address) (CName .anon) :=
  match resolve store p.2 with
  | some ref => if m.contains ref then m else m.insert ref (Ix.Kernel.roleKey p.1)
  | none => m

private theorem bindingsStep_preserves (store : Store)
    (m : Std.HashMap (ConstRef _root_.Address) (CName .anon))
    (p : Ix.Kernel.Role × _root_.Address) {ref₀ : ConstRef _root_.Address} {k₀ : CName .anon}
    (hm : m[ref₀]? = some k₀) :
    (bindingsStep store m p)[ref₀]? = some k₀ := by
  unfold bindingsStep
  cases resolve store p.2 with
  | none => exact hm
  | some ref =>
    by_cases hc : m.contains ref = true
    · rw [hc, if_pos rfl]; exact hm
    · rw [Bool.not_eq_true _ |>.mp hc, Bool.false_eq_true, if_neg (by decide)]
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
        have hstep : (bindingsStep (defCx ev).store m (ro, a)) = m := by
          unfold bindingsStep; rw [resolve_defCx_of_mem_pre ev ha_mem, hrp]
        rw [hstep]
        exact foldl_bindingsStep_lookup hblk l m hnone hlk
      | some ref =>
        simp only [hrp, Option.map_some, List.lookup_cons] at hlk
        by_cases heq : ref₀ == ref
        · rw [heq] at hlk
          injection hlk with hk
          subst hk
          have href_eq : ref = ref₀ := (beq_iff_eq.mp heq).symm
          subst href_eq
          have hstep : (bindingsStep (defCx ev).store m (ro, a))[ref₀]? = some (Ix.Kernel.roleKey ro) := by
            unfold bindingsStep
            rw [resolve_defCx_of_mem_pre ev ha_mem, hrp,
                Std.HashMap.contains_eq_isSome_getElem?, hnone]
            simp [Std.HashMap.getElem?_insert]
          exact foldl_bindingsStep_preserves (defCx ev).store l _ hstep
        · rw [Bool.not_eq_true _ |>.mp heq] at hlk
          have hstep_none : (bindingsStep (defCx ev).store m (ro, a))[ref₀]? = none := by
            unfold bindingsStep
            rw [resolve_defCx_of_mem_pre ev ha_mem, hrp]
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
        unfold bindingsStep
        cases hrs : resolve (defCx ev).store a with
        | none => exact hnone
        | some ref =>
          have hnot_blk := resolve_defCx_not_mem_pre ev hev_defn ha_not hrs
          have hne : ref ≠ ref₀ := fun h => hnot_blk (by rw [h]; exact hblk)
          split
          · exact hnone
          · rw [Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.mpr hne]
            exact hnone
      exact foldl_bindingsStep_lookup hblk l _ hstep_none hlk

private theorem defCx_roles_of_pure {ref : ConstRef _root_.Address} {k : CName .anon}
    (h : pureRolesLookup ref = some k) :
    (defCx ev).roles.names[ref]? = some k := by
  have hblk : constRefBlock ref ∈ committedPreAddrs :=
    pureRolesList_block_mem (ref, k) (mem_of_lookup_eq_some h)
  show (committedDefaultRoleTable.bound.foldl (bindingsStep (defCx ev).store) {})[ref]? = some k
  rw [← Array.foldl_toList]
  exact foldl_bindingsStep_lookup ev hev_defn hblk
    committedDefaultRoleTable.bound.toList {} Std.HashMap.getElem?_empty h

/-! ### Pure recursor index -/

private structure PureIdx where
  recs : List (ConstRef _root_.Address × RecEntry) := []
  blocks : List (_root_.Address × Array Nat) := []
  found : List (_root_.Address × Array (Nat × ConstRef _root_.Address)) := []

private def pureCandStep (owner : _root_.Address) (c : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (s : PureIdx) : Option PureIdx := do
  let (pos, rec) := member
  let ref : ConstRef _root_.Address := .member owner pos
  guard (s.recs.lookup ref).isNone
  guard (c.refs.toList.all committedPreAddrs.contains)
  let (motive, carriers, major) ← analyseRecursor preStorePure owner c rec
  let .member block firstIdx ← carriers[0]? | none
  guard (committedPreAddrs.contains block)
  let blockRec ← preStorePure block
  let .muts members := blockRec.info | none
  let indcs := Ix.CompileCert.ReaderIndex.inductives members
  let (_, first) ← indcs[0]?
  let order := Ix.CompileCert.ReaderIndex.orderFor carriers block indcs.size
  guard (Ix.CompileCert.ReaderIndex.orderValid firstIdx indcs order)
  guard (s.found.lookup block).isNone
  guard (s.blocks.lookup block).isNone
  let large := rec.lvls.toNat == first.lvls.toNat + 1
  let entry : RecEntry := ⟨block, motive, major, large⟩
  pure {
    recs := (ref, entry) :: s.recs
    blocks := (block, order) :: s.blocks
    found := (block, #[(motive, ref)]) :: s.found
  }

private def pureRecordIdxStep (rec : _root_.Address × Ixon.Constant) (s : PureIdx) :
    Option PureIdx :=
  match (recursorMembers rec.2).toList with
  | [] => some s
  | [m] => pureCandStep rec.1 rec.2 m s
  | _ => none

private def pureIndexRecords : List (_root_.Address × Ixon.Constant) → PureIdx → Option PureIdx
  | [], s => some s
  | r :: rs, s => do
    let s' ← pureRecordIdxStep r s
    pureIndexRecords rs s'

private def purePreIdx? : Option PureIdx :=
  pureIndexRecords committedPreludeList {}

private def pureRecsLookup (ref : ConstRef _root_.Address) : Option RecEntry := do
  let s ← purePreIdx?
  s.recs.lookup ref

private def pureBlocksLookup (b : _root_.Address) : Option BlockShape := do
  let s ← purePreIdx?
  let order ← s.blocks.lookup b
  let foundArr ← s.found.lookup b
  pure ⟨order, foundArr.map (·.2)⟩

private def IdxMatches (bs : Ix.CompileCert.ReaderIndex.BuildState) (s : PureIdx) : Prop :=
  (∀ r, bs.1.recs[r]? = s.recs.lookup r) ∧
  (∀ b, bs.1.blocks[b]? = (s.blocks.lookup b).map fun ord => ⟨ord, #[]⟩) ∧
  (∀ b, bs.2[b]? = s.found.lookup b)

private theorem headRef_defCx_eq_pure {owner : _root_.Address} {c : Ixon.Constant}
    (hrefs : c.refs.toList.all committedPreAddrs.contains = true) (e : Ixon.Expr) :
    headRef (defCx ev).store owner c e = headRef preStorePure owner c e := by
  unfold headRef
  cases appHead c spineFuel e with
  | ref i _ =>
    cases hget : c.refs[i.toNat]? with
    | none => rfl
    | some a =>
      have hmem : a ∈ c.refs.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)
      have hpa : a ∈ committedPreAddrs :=
        List.contains_iff_mem.mp (List.all_eq_true.mp hrefs a hmem)
      simp [bind, Option.bind, resolve_defCx_of_mem_pre ev hpa]
  | _ => rfl

private theorem analyseRecursor_defCx_eq_pure {owner : _root_.Address} {c : Ixon.Constant}
    (hrefs : c.refs.toList.all committedPreAddrs.contains = true) (r : Ixon.Recursor) :
    analyseRecursor (defCx ev).store owner c r = analyseRecursor preStorePure owner c r := by
  unfold analyseRecursor
  have hh := headRef_defCx_eq_pure ev hrefs
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

private def preInputIndexedBool : Bool :=
  committedPreludeList.all fun (a, c) =>
    (recursorMembers c).all fun (_, r) =>
      match analyseRecursor preStorePure a c r with
      | some (_, carriers, _) =>
        match carriers[0]? with
        | some (.member b _) => committedPreAddrs.contains b
        | _ => true
      | none => true

private theorem preInputIndexed_true : preInputIndexedBool = true := by
  decide +kernel

private theorem filter_committedPrelude_inputIndexed :
    let known : Std.HashSet _root_.Address :=
      committedPrelude.foldl (fun s (a, _) => s.insert a) {}
    committedPrelude.filter (fun (a, c) =>
      inputIndexed (defCx ev).store known ev a c) = committedPrelude := by
  intro known
  have hknown : ∀ x, known.contains x = true ↔ x ∈ committedPreAddrs := by
    intro x
    show (committedPrelude.foldl (fun s (a, _) => s.insert a) {}).contains x = true ↔ _
    rw [← Array.foldl_toList, show committedPrelude.toList = committedPreludeList from rfl]
    simpa [committedPreAddrs] using foldl_insert_contains committedPreludeList [] {} (by simp) x
  apply Array.ext'
  rw [Array.toList_filter, List.filter_eq_self]
  intro ⟨a, c⟩ hmem
  have hmem' : (a, c) ∈ committedPreludeList := hmem
  have hrefs : c.refs.toList.all committedPreAddrs.contains = true :=
    (Bool.and_eq_true.mp (List.all_eq_true.mp preRefsAndProjClosed (a, c) hmem')).1
  have hpure := List.all_eq_true.mp preInputIndexed_true (a, c) hmem'
  unfold inputIndexed
  apply Bool.or_eq_true.mpr
  left
  rw [Array.all_eq_true_iff_forall_mem] at hpure ⊢
  intro ⟨j, r⟩ hjr
  have hp := hpure (j, r) hjr
  rw [analyseRecursor_defCx_eq_pure ev hrefs r]
  cases analyseRecursor preStorePure a c r with
  | none => rfl
  | some triple =>
    rcases triple with ⟨m, carriers, major⟩
    dsimp only at hp ⊢
    cases carriers[0]? with
    | none => rfl
    | some cr =>
      cases cr with
      | ctor _ _ _ => rfl
      | member b idx =>
        dsimp only at hp ⊢
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
  dsimp only at hp
  cases hrnone : (s.recs.lookup (.member owner pos)).isNone with
  | false => simp [hrnone, guard] at hp
  | true =>
    simp only [hrnone, guard, ↓reduceIte, bind, Option.bind] at hp
    cases hrefs : c.refs.toList.all committedPreAddrs.contains with
    | false => simp [hrefs] at hp
    | true =>
      simp only [hrefs, ↓reduceIte] at hp
      cases han : analyseRecursor preStorePure owner c rec with
      | none => simp [han] at hp
      | some triple =>
        rcases triple with ⟨motive, carriers, major⟩
        simp only [han] at hp
        cases hc0 : carriers[0]? with
        | none => simp [hc0] at hp
        | some cr0 =>
          cases cr0 with
          | ctor _ _ _ => simp [hc0] at hp
          | member block firstIdx =>
            simp only [hc0] at hp
            cases hblk : committedPreAddrs.contains block with
            | false => simp [hblk] at hp
            | true =>
              simp only [hblk, ↓reduceIte] at hp
              cases hbrec : preStorePure block with
              | none => simp [hbrec] at hp
              | some blockRec =>
                simp only [hbrec] at hp
                cases hbi : blockRec.info with
                | defn _ | recr _ | axio _ | quot _ | cPrj _ | rPrj _ | iPrj _ | dPrj _ =>
                  simp [hbi] at hp
                | muts members =>
                  simp only [hbi] at hp
                  cases hind0 : (Ix.CompileCert.ReaderIndex.inductives members)[0]? with
                  | none => simp [hind0] at hp
                  | some ifirst =>
                    rcases ifirst with ⟨_, first⟩
                    simp only [hind0] at hp
                    cases hord : Ix.CompileCert.ReaderIndex.orderValid firstIdx
                        (Ix.CompileCert.ReaderIndex.inductives members)
                        (Ix.CompileCert.ReaderIndex.orderFor carriers block
                          (Ix.CompileCert.ReaderIndex.inductives members).size) with
                    | false => simp [hord] at hp
                    | true =>
                      simp only [hord, ↓reduceIte] at hp
                      cases hfnone : (s.found.lookup block).isNone with
                      | false => simp [hfnone] at hp
                      | true =>
                        simp only [hfnone, ↓reduceIte] at hp
                        cases hbnone : (s.blocks.lookup block).isNone with
                        | false => simp [hbnone] at hp
                        | true =>
                          simp only [hbnone, ↓reduceIte, pure, Option.some.injEq] at hp
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
                          have han_cx := analyseRecursor_defCx_eq_pure ev hrefs rec
                          have hst_blk := defCx_store_of_mem_pre ev (List.contains_iff_mem.mp hblk)
                          unfold Ix.CompileCert.ReaderIndex.candidate
                          dsimp only
                          rw [hr_cont]
                          dsimp only
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
                              (·.1 == motive) = false := rfl
                          rw [hany_empty]
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
                              rw [Bool.not_eq_true _ |>.mp he, hsym, hrecs r]
                          · intro b
                            rw [Std.HashMap.getElem?_insert, List.lookup_cons]
                            by_cases he : b == block
                            · have hsym : (block == b) = true :=
                                beq_iff_eq.mpr (beq_iff_eq.mp he).symm
                              simp [he, hsym]
                            · have hsym : (block == b) = false :=
                                beq_eq_false_iff_ne.mpr fun h => he (beq_iff_eq.mpr h.symm)
                              rw [Bool.not_eq_true _ |>.mp he, hsym, hblocks b]
                          · intro b
                            rw [Std.HashMap.getElem?_insert, List.lookup_cons]
                            by_cases he : b == block
                            · have hsym : (block == b) = true :=
                                beq_iff_eq.mpr (beq_iff_eq.mp he).symm
                              simp [he, hsym]
                            · have hsym : (block == b) = false :=
                                beq_eq_false_iff_ne.mpr fun h => he (beq_iff_eq.mpr h.symm)
                              rw [Bool.not_eq_true _ |>.mp he, hsym, hfound b]

private theorem forIn_recordStep_pre :
    ∀ (rs : List (_root_.Address × Ixon.Constant)) (s s' : PureIdx)
      (bs : Ix.CompileCert.ReaderIndex.BuildState),
      IdxMatches bs s →
      pureIndexRecords rs s = some s' →
      IdxMatches
        (forIn (m := Id) rs bs (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store)) s'
  | [], s, s', bs, hm, hp => by
    injection hp with hs
    subst hs
    exact hm
  | r :: rs, s, s', bs, hm, hp => by
    unfold pureIndexRecords at hp
    simp only [bind, Option.bind] at hp
    cases hrs : pureRecordIdxStep r s with
    | none => simp [hrs] at hp
    | some smid =>
      simp only [hrs] at hp
      rw [List.forIn_cons]
      unfold Ix.CompileCert.ReaderIndex.recordStep
      rw [← Array.forIn_toList]
      unfold pureRecordIdxStep at hrs
      cases hrm : (recursorMembers r.2).toList with
      | nil =>
        rw [hrm] at hrs ⊢
        injection hrs with hsm
        subst hsm
        exact forIn_recordStep_pre rs s s' bs hm hp
      | cons m tl =>
        cases tl with
        | cons _ _ => rw [hrm] at hrs; cases hrs
        | nil =>
          rw [hrm] at hrs ⊢
          simp only [List.forIn_cons, List.forIn_nil]
          have hmid := candidate_matches_of_pureCandStep ev hm hrs
          cases hcand : Ix.CompileCert.ReaderIndex.candidate (defCx ev).store r.1 r.2 m bs with
          | yield bs1 =>
            rw [hcand] at hmid
            exact forIn_recordStep_pre rs smid s' bs1 hmid hp
          | done bs1 =>
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
    rw [List.forIn_cons]
    unfold Ix.CompileCert.ReaderIndex.recordStep
    rw [hrm]
    exact forIn_recordStep_ev_noop rs bs fun p hp => hd p (List.mem_cons_of_mem _ hp)

private theorem forIn_completeStep_recs :
    ∀ (es : List (_root_.Address × Array (Nat × ConstRef _root_.Address))) (idx : RecIndex),
      (forIn (m := Id) es idx Ix.CompileCert.ReaderIndex.completeStep).recs = idx.recs
  | [], _ => rfl
  | e :: es, idx => by
    rw [List.forIn_cons]
    unfold Ix.CompileCert.ReaderIndex.completeStep
    exact forIn_completeStep_recs es _

private theorem qsort_singleton {α : Type} (x : α) (lt : α → α → Bool) :
    #[x].qsort lt = #[x] := rfl

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
    · exact hdone
  | (k, arr) :: es, idx, hes, hord, hor => by
    rw [List.forIn_cons]
    unfold Ix.CompileCert.ReaderIndex.completeStep
    dsimp only
    by_cases hkb : k = b
    · subst hkb
      have harr_some := hes (k, arr) List.mem_cons_self
      rw [hf] at harr_some
      injection harr_some with harr
      subst harr
      rw [qsort_singleton]
      have hmap : (#[(m, ref)].map (·.2)) = #[ref] := rfl
      rw [hmap]
      let idx' : RecIndex :=
        { idx with blocks := idx.blocks.insert k { idx.blocks.getD k default with recs := #[ref] } }
      have hdone : idx'.blocks[k]? = some ⟨order, #[ref]⟩ := by
        show (idx.blocks.insert k { idx.blocks.getD k default with recs := #[ref] })[k]? = _
        rw [Std.HashMap.getElem?_insert_self]
        cases idx.blocks.getD k default with
        | mk ord rcs =>
          dsimp only at hord ⊢
          rw [hord]
      have hord' : (idx'.blocks.getD k default).order = order := by
        rw [Std.HashMap.getD_eq_getD_getElem?, hdone]; rfl
      exact forIn_completeStep_block hf es idx'
        (fun e he => hes e (List.mem_cons_of_mem _ he)) hord' (.inr hdone)
    · let idx' : RecIndex :=
        { idx with blocks := idx.blocks.insert k
            { idx.blocks.getD k default with
              recs := (arr.qsort (fun l r => l.1 < r.1)).map (·.2) } }
      have hsame : idx'.blocks[b]? = idx.blocks[b]? := by
        show (idx.blocks.insert k _)[b]? = _
        exact Std.HashMap.getElem?_insert_of_ne hkb
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

private theorem purePreIdx_found_singletons :
    match purePreIdx? with
    | some s => (s.found.all fun (_, arr) => arr.size == 1) = true
    | none => False := by
  decide +kernel

private theorem collected_matches_purePreIdx {s : PureIdx} (hs : purePreIdx? = some s) :
    IdxMatches
      (forIn (m := Id) (indexedRecords (defCx ev).store committedPrelude ev)
        (({} : RecIndex), ({} : Ix.CompileCert.ReaderIndex.Found))
        (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store)) s := by
  unfold indexedRecords
  rw [filter_committedPrelude_inputIndexed ev, ← Array.forIn_toList, Array.toList_append,
      List.forIn_append, show committedPrelude.toList = committedPreludeList from rfl]
  have hinit : IdxMatches (({} : RecIndex), ({} : Ix.CompileCert.ReaderIndex.Found)) {} :=
    ⟨fun _ => Std.HashMap.getElem?_empty,
     fun _ => Std.HashMap.getElem?_empty,
     fun _ => Std.HashMap.getElem?_empty⟩
  have hpre := forIn_recordStep_pre ev committedPreludeList {} s _ hinit hs
  have hev_filt : ∀ p ∈ (ev.filter _).toList, ∃ d, p.2.info = .defn d := by
    intro p hp
    rw [Array.toList_filter] at hp
    exact hev_defn p (List.mem_of_mem_filter hp)
  rw [forIn_recordStep_ev_noop ev _ _ hev_filt]
  exact hpre

private theorem defCx_index_recs_of_pure {ref : ConstRef _root_.Address} {entry : RecEntry}
    (h : pureRecsLookup ref = some entry) :
    (defCx ev).index.recs[ref]? = some entry := by
  unfold pureRecsLookup at h
  cases hs : purePreIdx? with
  | none => simp [hs] at h
  | some s =>
    simp only [hs, bind, Option.bind] at h
    show (buildIndex (defCx ev).store
      (indexedRecords (defCx ev).store committedPrelude ev)).recs[ref]? = some entry
    rw [← Ix.CompileCert.ReaderIndex.run_eq]
    unfold Ix.CompileCert.ReaderIndex.run
    rw [forIn_completeStep_recs]
    exact (collected_matches_purePreIdx ev hev_defn hs).1 ref |>.trans h

private theorem defCx_index_blocks_of_pure {b : _root_.Address} {sh : BlockShape}
    (h : pureBlocksLookup b = some sh) :
    (defCx ev).index.blocks[b]? = some sh := by
  unfold pureBlocksLookup at h
  cases hs : purePreIdx? with
  | none => simp [hs] at h
  | some s =>
    simp only [hs, bind, Option.bind] at h
    cases hob : s.blocks.lookup b with
    | none => simp [hob] at h
    | some order =>
      simp only [hob] at h
      cases hfb : s.found.lookup b with
      | none => simp [hfb] at h
      | some foundArr =>
        simp only [hfb, pure, Option.some.injEq] at h
        subst h
        have hsing := purePreIdx_found_singletons
        rw [hs] at hsing
        have hmem_f := mem_of_lookup_eq_some hfb
        have hsz : foundArr.size = 1 :=
          beq_iff_eq.mp (List.all_eq_true.mp hsing (b, foundArr) hmem_f)
        obtain ⟨⟨m, ref⟩, rfl⟩ : ∃ x, foundArr = #[x] := by
          cases foundArr with
          | mk l =>
            cases l with
            | nil => cases hsz
            | cons x tl =>
              cases tl with
              | nil => exact ⟨x, rfl⟩
              | cons _ _ => simp at hsz
        have hcm := collected_matches_purePreIdx ev hev_defn hs
        show (buildIndex (defCx ev).store
          (indexedRecords (defCx ev).store committedPrelude ev)).blocks[b]? = _
        rw [← Ix.CompileCert.ReaderIndex.run_eq]
        unfold Ix.CompileCert.ReaderIndex.run
        let collected := forIn (m := Id) (indexedRecords (defCx ev).store committedPrelude ev)
          (({} : RecIndex), ({} : Ix.CompileCert.ReaderIndex.Found))
          (Ix.CompileCert.ReaderIndex.recordStep (defCx ev).store)
        have hf_col : collected.2[b]? = some #[(m, ref)] := (hcm.2.2 b).trans hfb
        have hb_col : collected.1.blocks[b]? = some ⟨order, #[]⟩ := by
          rw [hcm.2.1 b, hob]; rfl
        have hord_col : (collected.1.blocks.getD b default).order = order := by
          rw [Std.HashMap.getD_eq_getD_getElem?, hb_col]; rfl
        have hmem_toList : (b, #[(m, ref)]) ∈ collected.2.toList :=
          Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hf_col
        exact forIn_completeStep_block hf_col collected.2.toList collected.1
          (fun e he => Std.HashMap.mem_toList_iff_getElem?_eq_some.mp he)
          hord_col (.inl hmem_toList)

/-! ### Pure record and stream simulation on `committedPrelude` -/

private def pureMemberKey (r : ConstRef _root_.Address) : ReadM (CName .anon) :=
  match pureRolesLookup r with
  | some k => pure k
  | none => malformed "unbound"

private theorem pureMemberKey_sound {r : ConstRef _root_.Address} {k : CName .anon}
    (h : pureMemberKey r = .ok k) :
    (defCx ev).memberKey r = .ok k := by
  unfold pureMemberKey at h
  cases hp : pureRolesLookup r with
  | none => rw [hp] at h; cases h
  | some k' =>
    rw [hp] at h
    injection h with hk
    subst hk
    exact Ctx.memberKey_of_role (defCx_roles_of_pure ev hev_defn hp)

private def pureKeyAt (a : _root_.Address) : ReadM (CName .anon) := do
  if committedPreAddrs.contains a then
    match resolve preStorePure a with
    | some r =>
      match pureRolesLookup r with
      | some k => pure k
      | none => malformed "unbound"
    | none => malformed "unresolved"
  else malformed "outside prelude"

private theorem pureKeyAt_sound {a : _root_.Address} {k : CName .anon}
    (h : pureKeyAt a = .ok k) :
    (defCx ev).keyAt a = .ok k := by
  unfold pureKeyAt at h
  split at h
  · rename_i hpa
    have ha_mem : a ∈ committedPreAddrs := List.contains_iff_mem.mp hpa
    cases hr : resolve preStorePure a with
    | none => rw [hr] at h; cases h
    | some r =>
      rw [hr] at h
      cases hk : pureRolesLookup r with
      | none => rw [hk] at h; cases h
      | some k' =>
        rw [hk] at h
        injection h with hkeq
        subst hkeq
        rw [Ctx.keyAt_eq_ok]
        unfold keyOfAddress
        rw [resolve_defCx_of_mem_pre ev ha_mem, hr, defCx_roles_of_pure ev hev_defn hk]
  · cases h

private structure PureECx where
  src : Ixon.Constant
  univs : Array CLevel
  self : Nat → Option (ReadM (CName .anon))

private def PureECx.toECx (pe : PureECx) (realSelf : Nat → Option (ReadM (CName .anon))) :
    ECx .anon :=
  ⟨defCx ev, pe.src, pe.univs, realSelf⟩

private def PureECx.level (pe : PureECx) (i : UInt64) : ReadM CLevel :=
  match pe.univs[i.toNat]? with
  | some l => pure l
  | none => malformed "universe table index is out of bounds"

private def PureECx.levels (pe : PureECx) (us : Array UInt64) : ReadM (List CLevel) :=
  us.toList.mapM pe.level

private def PureECx.keyAt (pe : PureECx) (i : UInt64) : ReadM (CName .anon) := do
  let some a := pe.src.refs[i.toNat]? | malformed "reference index is out of bounds"
  pureKeyAt a

private def pureConvExpr (pe : PureECx) (tbl : Array (ReadM (CExpr .anon))) :
    Ixon.Expr → ReadM (CExpr .anon)
  | .var i => pure (Ix.Kernel.Expr.mkBvar i.toNat)
  | .sort i => do pure (.sort (← pe.level i))
  | .ref i us => do
    let k ← pe.keyAt i
    pure (.const k (← pe.levels us))
  | .recur i us => do
    let some n := pe.self i.toNat | malformed "recursive reference is outside its block"
    pure (.const (← n) (← pe.levels us))
  | .prj i field v => do
    let k ← pe.keyAt i
    pure (.proj k field.toNat (← pureConvExpr pe tbl v))
  | .str _ => malformed "unexpected str in prelude"
  | .nat _ => malformed "unexpected nat in prelude"
  | .app f a => do pure (.app (← pureConvExpr pe tbl f) (← pureConvExpr pe tbl a))
  | .lam t b => do
    pure (.lam (← pureConvExpr pe tbl t) (← pureConvExpr pe tbl b) Ix.Kernel.BinderMeta.leanNever)
  | .all t b => do
    pure (.forallE (← pureConvExpr pe tbl t) (← pureConvExpr pe tbl b) Ix.Kernel.BinderMeta.leanNever)
  | .letE nonDep _ t v b => do
    pure (.letE (← pureConvExpr pe tbl t) (← pureConvExpr pe tbl v) (← pureConvExpr pe tbl b) { nonDep })
  | .share i =>
    match tbl[i.toNat]? with
    | some r => r
    | none => malformed "sharing reference is not to an earlier entry"

private theorem except_bind_ok_inv {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem pureConvExpr_sound {pe : PureECx}
    {realSelf : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i m k, pe.self i = some m → m = .ok k → ∃ rm, realSelf i = some rm ∧ rm = .ok k)
    {ptbl rtbl : Array (ReadM (CExpr .anon))}
    (htbl : ∀ i e, ptbl[i]? = some (.ok e) → rtbl[i]? = some (.ok e)) :
    ∀ (expr : Ixon.Expr) {out : CExpr .anon},
      pureConvExpr pe ptbl expr = .ok out →
      convExpr (pe.toECx ev realSelf) rtbl expr = .ok out
  | .var i, _, h => h
  | .sort i, _, h => h
  | .ref i us, _, h => by
    unfold pureConvExpr at h
    obtain ⟨k, hk, hrest⟩ := except_bind_ok_inv h
    obtain ⟨ls, hls, hpure⟩ := except_bind_ok_inv hrest
    injection hpure with hout; subst hout
    unfold PureECx.keyAt at hk
    cases href : pe.src.refs[i.toNat]? with
    | none => rw [href] at hk; cases hk
    | some a =>
      rw [href] at hk
      have hreal_k := pureKeyAt_sound ev hev_defn hk
      unfold convExpr ECx.keyAt PureECx.toECx ECx.levels
      simp only [href, bind, Except.bind]
      rw [hreal_k]
      change (ls <$ pure ()) = _ at hpure
      simp only [hls, pure, Except.pure]
  | .recur i us, _, h => by
    unfold pureConvExpr at h
    cases hs : pe.self i.toNat with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      dsimp only at h
      obtain ⟨k, hm, hrest⟩ := except_bind_ok_inv h
      obtain ⟨ls, hls, hpure⟩ := except_bind_ok_inv hrest
      injection hpure with hout; subst hout
      obtain ⟨rm, hrs, hrm⟩ := hself i.toNat m k hs hm
      unfold convExpr PureECx.toECx ECx.levels
      simp only [hrs, hrm, hls, bind, Except.bind, pure, Except.pure]
  | .prj i field v, _, h => by
    unfold pureConvExpr at h
    obtain ⟨k, hk, hrest⟩ := except_bind_ok_inv h
    obtain ⟨ve, hve, hpure⟩ := except_bind_ok_inv hrest
    injection hpure with hout; subst hout
    unfold PureECx.keyAt at hk
    cases href : pe.src.refs[i.toNat]? with
    | none => rw [href] at hk; cases hk
    | some a =>
      rw [href] at hk
      have hreal_k := pureKeyAt_sound ev hev_defn hk
      have ihv := pureConvExpr_sound hself htbl v hve
      unfold convExpr ECx.keyAt PureECx.toECx
      simp only [href, hreal_k, ihv, bind, Except.bind, pure, Except.pure]
  | .str _, _, h => by cases h
  | .nat _, _, h => by cases h
  | .app f a, _, h => by
    unfold pureConvExpr at h
    obtain ⟨fe, hfe, hrest⟩ := except_bind_ok_inv h
    obtain ⟨ae, hae, hpure⟩ := except_bind_ok_inv hrest
    injection hpure with hout; subst hout
    have ihf := pureConvExpr_sound hself htbl f hfe
    have iha := pureConvExpr_sound hself htbl a hae
    simp [convExpr, ihf, iha, bind, Except.bind, pure, Except.pure]
  | .lam t b, _, h => by
    unfold pureConvExpr at h
    obtain ⟨te, hte, hrest⟩ := except_bind_ok_inv h
    obtain ⟨be, hbe, hpure⟩ := except_bind_ok_inv hrest
    injection hpure with hout; subst hout
    have iht := pureConvExpr_sound hself htbl t hte
    have ihb := pureConvExpr_sound hself htbl b hbe
    simp [convExpr, iht, ihb, bind, Except.bind, pure, Except.pure]
  | .all t b, _, h => by
    unfold pureConvExpr at h
    obtain ⟨te, hte, hrest⟩ := except_bind_ok_inv h
    obtain ⟨be, hbe, hpure⟩ := except_bind_ok_inv hrest
    injection hpure with hout; subst hout
    have iht := pureConvExpr_sound hself htbl t hte
    have ihb := pureConvExpr_sound hself htbl b hbe
    simp [convExpr, iht, ihb, bind, Except.bind, pure, Except.pure]
  | .letE nonDep mode t v b, _, h => by
    unfold pureConvExpr at h
    obtain ⟨te, hte, hr1⟩ := except_bind_ok_inv h
    obtain ⟨ve, hve, hr2⟩ := except_bind_ok_inv hr1
    obtain ⟨be, hbe, hpure⟩ := except_bind_ok_inv hr2
    injection hpure with hout; subst hout
    have iht := pureConvExpr_sound hself htbl t hte
    have ihv := pureConvExpr_sound hself htbl v hve
    have ihb := pureConvExpr_sound hself htbl b hbe
    simp [convExpr, iht, ihv, ihb, bind, Except.bind, pure, Except.pure]
  | .share i, _, h => by
    unfold pureConvExpr at h
    cases hget : ptbl[i.toNat]? with
    | none => rw [hget] at h; cases h
    | some r =>
      rw [hget] at h
      subst h
      have hr := htbl i.toNat _ hget
      simp [convExpr, hr]

private def pureBuildTbl (pe : PureECx) : List Ixon.Expr → Array (ReadM (CExpr .anon)) →
    Array (ReadM (CExpr .anon))
  | [], tbl => tbl
  | e :: es, tbl => pureBuildTbl pe es (tbl.push (pureConvExpr pe tbl e))

private def pureReadExpr (src : Ixon.Constant) (param : Nat → Ix.Kernel.LevelParam)
    (self : Nat → Option (ReadM (CName .anon))) (e : Ixon.Expr) : ReadM (CExpr .anon) :=
  let pe : PureECx := ⟨src, src.univs.map (convUniv param), self⟩
  let tbl := pureBuildTbl pe src.sharing.toList #[]
  pureConvExpr pe tbl e

private theorem realBuildTbl_eq (ecx : ECx .anon) (src : Ixon.Constant) :
    (MemberReader.mk' ecx.cx src (fun _ => 0) ecx.self) =
      MemberReader.mk' ecx.cx src (fun _ => 0) ecx.self := rfl

private theorem forIn_sharing_tbl {pe : PureECx}
    {realSelf : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i m k, pe.self i = some m → m = .ok k → ∃ rm, realSelf i = some rm ∧ rm = .ok k) :
    ∀ (es : List Ixon.Expr) (ptbl rtbl : Array (ReadM (CExpr .anon))),
      ptbl.size = rtbl.size →
      (∀ i e, ptbl[i]? = some (.ok e) → rtbl[i]? = some (.ok e)) →
      (∀ i e, (pureBuildTbl pe es ptbl)[i]? = some (.ok e) →
        (forIn (m := Id) es rtbl (fun entry tbl =>
          pure (.yield (tbl.push (convExpr (pe.toECx ev realSelf) tbl entry)))))[i]? = some (.ok e))
  | [], ptbl, rtbl, _, htbl => htbl
  | entry :: es, ptbl, rtbl, hsz, htbl => by
    rw [List.forIn_cons]
    dsimp only [pureBuildTbl, bind, pure]
    refine forIn_sharing_tbl hself es
      (ptbl.push (pureConvExpr pe ptbl entry))
      (rtbl.push (convExpr (pe.toECx ev realSelf) rtbl entry))
      (by simp [hsz]) ?_
    intro i e hi
    rw [Array.getElem?_push] at hi ⊢
    by_cases heq : i = ptbl.size
    · rw [if_pos heq] at hi
      rw [← hsz, if_pos heq]
      injection hi with hok
      exact congrArg some (pureConvExpr_sound ev hev_defn hself htbl entry hok)
    · rw [if_neg heq] at hi
      rw [← hsz, if_neg heq]
      exact htbl i e hi

private theorem pureReadExpr_sound {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {pself rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i m k, pself i = some m → m = .ok k → ∃ rm, rself i = some rm ∧ rm = .ok k)
    {expr : Ixon.Expr} {out : CExpr .anon}
    (h : pureReadExpr src param pself expr = .ok out) :
    (MemberReader.mk' (defCx ev) src param rself).read expr = .ok out := by
  let pe : PureECx := ⟨src, src.univs.map (convUniv param), pself⟩
  have hmk : (MemberReader.mk' (defCx ev) src param rself).tbl =
      forIn (m := Id) src.sharing.toList (#[] : Array (ReadM (CExpr .anon)))
        (fun entry tbl => pure (.yield (tbl.push (convExpr (pe.toECx ev rself) tbl entry)))) := by
    unfold MemberReader.mk' Id.run
    rw [← Array.forIn_toList]
    rfl
  unfold MemberReader.read
  have hecx : (MemberReader.mk' (defCx ev) src param rself).ecx = pe.toECx ev rself := rfl
  rw [hecx, hmk]
  exact pureConvExpr_sound ev hev_defn hself
    (forIn_sharing_tbl ev hev_defn hself src.sharing.toList #[] #[] rfl (fun _ _ h0 => by simp at h0))
    expr h

private def pureReadRecRules (src : Ixon.Constant) (param : Nat → Ix.Kernel.LevelParam)
    (pself : Nat → Option (ReadM (CName .anon))) (mb : _root_.Address) (mi : Nat) :
    List (Ixon.RecursorRule × Nat) → ReadM (List (Ix.Kernel.RecRule .anon))
  | [] => pure []
  | (rule, k) :: rest => do
    let ck ← pureMemberKey (.ctor mb mi k)
    let rhs ← pureReadExpr src param pself rule.rhs
    let tail ← pureReadRecRules src param pself mb mi rest
    pure (Ix.Kernel.RecRule.mk ck rule.fields.toNat 0 .inert rhs false false false :: tail)

private def pureReadRecursor (blockLps : List Ix.Kernel.LevelParam) (ref : ConstRef _root_.Address)
    (entry : RecEntry) : ReadM (CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon)) := do
  let .member rOwner j := ref | malformed "recursor reference is a constructor"
  if !committedPreAddrs.contains rOwner then malformed "recursor outside prelude"
  let some rc := preStorePure rOwner | malformed "recursor record is missing"
  let some (_, r) := (recursorMembers rc).find? (·.1 == j) | malformed "recursor member is missing"
  if r.isUnsafe then declined "unsafe inductive declaration"
  let key ← pureMemberKey ref
  let pself : Nat → Option (ReadM (CName .anon)) := fun i => match rc.info with
    | .muts rms => if i < rms.size then some (pureMemberKey (.member rOwner i)) else none
    | _ => if i == 0 then some (pure key) else none
  let lps := recLps entry.large blockLps
  let typ ← pureReadExpr rc (recParam lps) pself r.typ
  let cv : CVal .anon := ⟨key, lps, typ⟩
  let .member mb mi := entry.major | malformed "recursor major is a constructor"
  if !committedPreAddrs.contains mb then malformed "major outside prelude"
  let some major := inductiveAt preStorePure entry.major | declined "major not ind"
  unless major.ctors.size == r.rules.size do malformed "rule count"
  let rules ← pureReadRecRules rc (recParam lps) pself mb mi r.rules.zipIdx.toList
  pure (cv, ⟨r.params.toNat, r.motives.toNat, r.minors.toNat, r.indices.toNat, r.k,
    some entry.motive⟩, rules)

private theorem forIn_recRules_append {src : Ixon.Constant} {param : Nat → Ix.Kernel.LevelParam}
    {pself rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i m k, pself i = some m → m = .ok k → ∃ rm, rself i = some rm ∧ rm = .ok k)
    {mb : _root_.Address} {mi : Nat} :
    ∀ (l : List (Ixon.RecursorRule × Nat)) (acc tail : List (Ix.Kernel.RecRule .anon)),
      pureReadRecRules src param pself mb mi l = .ok tail →
      forIn l acc (fun (rule, k) rules => do
        let ck ← (defCx ev).memberKey (.ctor mb mi k)
        let rhs ← (MemberReader.mk' (defCx ev) src param rself).read rule.rhs
        pure (.yield (rules ++ [Ix.Kernel.RecRule.mk ck rule.fields.toNat 0 .inert rhs false false false]))) =
        .ok (acc ++ tail)
  | [], acc, tail, h => by
    injection h with ht; subst ht
    simp [pure, Except.pure]
  | (rule, k) :: rest, acc, tail, h => by
    unfold pureReadRecRules at h
    obtain ⟨ck, hck, hr1⟩ := except_bind_ok_inv h
    obtain ⟨rhs, hrhs, hr2⟩ := except_bind_ok_inv hr1
    obtain ⟨rtail, hrtail, hpure⟩ := except_bind_ok_inv hr2
    injection hpure with ht; subst ht
    have hck' := pureMemberKey_sound ev hev_defn hck
    have hrhs' := pureReadExpr_sound ev hev_defn hself hrhs
    rw [List.forIn_cons]
    simp only [hck', hrhs', bind, Except.bind, pure, Except.pure]
    rw [forIn_recRules_append hself rest _ rtail hrtail, List.append_assoc, List.singleton_append]

private theorem pureReadRecursor_sound {blockLps : List Ix.Kernel.LevelParam}
    {ref : ConstRef _root_.Address} {entry : RecEntry}
    {out : CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon)}
    (h : pureReadRecursor blockLps ref entry = .ok out) :
    readRecursor (defCx ev) blockLps ref entry = .ok out := by
  unfold pureReadRecursor at h
  cases ref with
  | ctor _ _ _ => cases h
  | member rOwner j =>
    dsimp only at h
    cases hro : committedPreAddrs.contains rOwner with
    | false => simp [hro] at h
    | true =>
      simp only [hro, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hrc : preStorePure rOwner with
      | none => rw [hrc] at h; cases h
      | some rc =>
        rw [hrc] at h
        dsimp only at h
        cases hfind : (recursorMembers rc).find? (·.1 == j) with
        | none => rw [hfind] at h; cases h
        | some jr =>
          rcases jr with ⟨_, r⟩
          rw [hfind] at h
          dsimp only at h
          cases hu : r.isUnsafe with
          | true => simp [hu] at h
          | false =>
            simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨key, hkey, hr1⟩ := except_bind_ok_inv h
            obtain ⟨typ, htyp, hr2⟩ := except_bind_ok_inv hr1
            cases hmaj : entry.major with
            | ctor _ _ _ => rw [hmaj] at hr2; cases hr2
            | member mb mi =>
              rw [hmaj] at hr2
              dsimp only at hr2
              cases hmb : committedPreAddrs.contains mb with
              | false => simp [hmb] at hr2
              | true =>
                simp only [hmb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hr2
                cases hind : inductiveAt preStorePure (.member mb mi) with
                | none => rw [hind] at hr2; cases hr2
                | some major =>
                  rw [hind] at hr2
                  dsimp only at hr2
                  cases hsz : (major.ctors.size == r.rules.size) with
                  | false => simp [hsz] at hr2
                  | true =>
                    simp only [hsz, ↓reduceIte] at hr2
                    obtain ⟨rules, hrules, hpure⟩ := except_bind_ok_inv hr2
                    injection hpure with hout; subst hout
                    have hkey' := pureMemberKey_sound ev hev_defn hkey
                    let pself : Nat → Option (ReadM (CName .anon)) := fun i => match rc.info with
                      | .muts rms => if i < rms.size then some (pureMemberKey (.member rOwner i)) else none
                      | _ => if i == 0 then some (pure key) else none
                    let rself : Nat → Option (ReadM (CName .anon)) := fun i => match rc.info with
                      | .muts rms => if i < rms.size then some ((defCx ev).memberKey (.member rOwner i)) else none
                      | _ => if i == 0 then some (pure key) else none
                    have hself : ∀ i m k, pself i = some m → m = .ok k → ∃ rm, rself i = some rm ∧ rm = .ok k := by
                      intro i m k hps hm
                      dsimp only [pself, rself] at hps ⊢
                      cases rc.info with
                      | muts rms =>
                        split at hps
                        · injection hps with hps; subst hps
                          exact ⟨_, rfl, pureMemberKey_sound ev hev_defn hm⟩
                        · cases hps
                      | _ =>
                        split at hps
                        · injection hps with hps; subst hps
                          exact ⟨_, rfl, hm⟩
                        · cases hps
                    have htyp' := pureReadExpr_sound ev hev_defn hself htyp
                    have hst_ro := defCx_store_of_mem_pre ev (List.contains_iff_mem.mp hro)
                    have hind_cx : inductiveAt (defCx ev).store (.member mb mi) = some major := by
                      unfold inductiveAt at hind ⊢
                      rw [defCx_store_of_mem_pre ev (List.contains_iff_mem.mp hmb)]
                      exact hind
                    unfold readRecursor
                    rw [hst_ro, hrc]
                    dsimp only
                    rw [hfind]
                    simp only [hu, Bool.false_eq_true, ↓reduceIte, hkey', htyp', hmaj, hind_cx, hsz,
                      bind, Except.bind, pure, Except.pure]
                    rw [← Array.forIn_toList, forIn_recRules_append ev hev_defn hself _ [] rules hrules,
                        List.nil_append]
                    rfl

/-! ### Pure single-type non-modelled inductive block reader (covers all 7 prelude blocks) -/

private def pureReadCtorList (owner : _root_.Address) (src : Ixon.Constant)
    (pself : Nat → Option (ReadM (CName .anon))) (nPd : Nat) :
    List (Ixon.Constructor × Nat) → ReadM (List (CVal .anon × Nat × Nat) × List (CName .anon))
  | [] => pure ([], [])
  | (ctor, j) :: rest => do
    unless ctor.cidx.toNat == j do malformed "cidx"
    if ctor.isUnsafe then declined "unsafe"
    let ck ← pureMemberKey (.ctor owner 0 j)
    let cty ← pureReadExpr src id pself ctor.typ
    let cv : CVal .anon := ⟨ck, List.range ctor.lvls.toNat, cty⟩
    unless nPd + ctor.fields.toNat == piTeleLen cv.type do malformed "fields"
    let (ctors, names) ← pureReadCtorList owner src pself nPd rest
    pure ((cv, ctor.params.toNat, ctor.fields.toNat) :: ctors, cv.name :: names)

private theorem forIn_ctors_sound {owner : _root_.Address} {src : Ixon.Constant}
    {pself rself : Nat → Option (ReadM (CName .anon))}
    (hself : ∀ i m k, pself i = some m → m = .ok k → ∃ rm, rself i = some rm ∧ rm = .ok k)
    {nPd : Nat} :
    ∀ (l : List (Ixon.Constructor × Nat))
      (accC : Array (CVal .anon × Nat × Nat)) (accN : List (CName .anon))
      (outC : List (CVal .anon × Nat × Nat)) (outN : List (CName .anon)),
      pureReadCtorList owner src pself nPd l = .ok (outC, outN) →
      forIn l ⟨accC, accN⟩ (fun (ctor, j) s => do
        unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
        if ctor.isUnsafe then declined "unsafe inductive declaration"
        let cv : CVal .anon :=
          ⟨← (defCx ev).memberKey (.ctor owner 0 j), List.range ctor.lvls.toNat,
            ← (MemberReader.mk' (defCx ev) src id rself).read ctor.typ⟩
        unless nPd + ctor.fields.toNat == piTeleLen cv.type do
          malformed s!"constructor {cv.name} declares {ctor.fields} fields at {nPd} parameters; its type has {piTeleLen cv.type} binders"
        pure (.yield ⟨s.1.push (cv, ctor.params.toNat, ctor.fields.toNat), s.2 ++ [cv.name]⟩)) =
        .ok ⟨accC ++ outC.toArray, accN ++ outN⟩
  | [], accC, accN, outC, outN, h => by
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    simp [pure, Except.pure]
  | (ctor, j) :: rest, accC, accN, outC, outN, h => by
    unfold pureReadCtorList at h
    cases hcj : (ctor.cidx.toNat == j) with
    | false => simp [hcj] at h
    | true =>
      simp only [hcj, ↓reduceIte] at h
      cases hcu : ctor.isUnsafe with
      | true => simp [hcu] at h
      | false =>
        simp only [hcu, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨ck, hck, hr1⟩ := except_bind_ok_inv h
        obtain ⟨cty, hcty, hr2⟩ := except_bind_ok_inv hr1
        dsimp only at hr2
        cases hfl : (nPd + ctor.fields.toNat == piTeleLen cty) with
        | false => simp [hfl] at hr2
        | true =>
          simp only [hfl, ↓reduceIte] at hr2
          obtain ⟨⟨tailC, tailN⟩, htail, hpure⟩ := except_bind_ok_inv hr2
          injection hpure with hp; injection hp with h1 h2; subst h1; subst h2
          have hck' := pureMemberKey_sound ev hev_defn hck
          have hcty' := pureReadExpr_sound ev hev_defn hself hcty
          rw [List.forIn_cons]
          simp only [hcj, ↓reduceIte, hcu, Bool.false_eq_true, hck', hcty', hfl,
            bind, Except.bind, pure, Except.pure]
          rw [forIn_ctors_sound hself rest _ _ tailC tailN htail]
          have hap : accC.push (⟨ck, List.range ctor.lvls.toNat, cty⟩, ctor.params.toNat, ctor.fields.toNat) ++
              tailC.toArray =
              accC ++ ((⟨ck, List.range ctor.lvls.toNat, cty⟩, ctor.params.toNat, ctor.fields.toNat) :: tailC).toArray := by
            apply Array.ext'
            simp [List.append_assoc]
          rw [hap, List.append_assoc, List.singleton_append]

private def pureLowerNoModel (rb : BlockRead .anon) : ReadM (Read .anon) := do
  let ⟨nPd, types, ctors, ctorNames, recs⟩ := rb
  let memberNames := types.toList.map (·.1.name)
  let fieldDoms := ctors.toList.flatMap fun (cv, _, _) =>
    (Ix.Kernel.Frontend.stripPisAll cv.type).1.map (·.1)
  let isRec := fieldDoms.any fun d => memberNames.any (Ix.Kernel.Frontend.occursConstFast · d)
  let isReflexive := fieldDoms.any fun d =>
    let (bs, body) := Ix.Kernel.Frontend.stripPisAll d
    !bs.isEmpty && memberNames.any (Ix.Kernel.Frontend.headIs · body)
  let numNested := match recs[0]? with
    | some (_, r, _) => r.motives - types.size
    | none => 0
  let b : Ix.Kernel.Frontend.InModel.BlockRec .anon :=
    ⟨types.toList.zip ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
        { cv, nP, nIdx, ctors := cs, isRec, isReflexive, numNested },
     ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
     recs.toList.map fun (cv, r, rules) =>
       { cv, nP := r.params, nM := r.motives, nm := r.minors, nI := r.indices, rules }⟩
  if Ix.Kernel.Frontend.InModel.wants b then
    declined "unexpected InModel.wants in prelude"
  else
    let r ← lowerInductiveDecls ({} : State .anon) rb
    if nodupNat ((r.decls.toList.flatMap Ix.Kernel.Declaration.names).map cnameCode) then
      pure r
    else
      declined "duplicate key"

private theorem pureLowerNoModel_sound {rb : BlockRead .anon} {r : Read .anon}
    (h : pureLowerNoModel rb = .ok r) (st : State .anon) :
    lowerInductive st rb = .ok r := by
  unfold pureLowerNoModel at h
  rcases rb with ⟨nPd, types, ctors, ctorNames, recs⟩
  dsimp only at h
  split at h
  · cases h
  · rename_i hwants_not
    have hwants : Ix.Kernel.Frontend.InModel.wants
        ⟨types.toList.zip ctorNames.toList |>.map fun ((cv, nP, nIdx), cs) =>
            { cv, nP, nIdx, ctors := cs,
              isRec := (ctors.toList.flatMap fun (cv, _, _) =>
                (Ix.Kernel.Frontend.stripPisAll cv.type).1.map (·.1)).any fun d =>
                  (types.toList.map (·.1.name)).any (Ix.Kernel.Frontend.occursConstFast · d),
              isReflexive := (ctors.toList.flatMap fun (cv, _, _) =>
                (Ix.Kernel.Frontend.stripPisAll cv.type).1.map (·.1)).any fun d =>
                  let (bs, body) := Ix.Kernel.Frontend.stripPisAll d
                  !bs.isEmpty && (types.toList.map (·.1.name)).any (Ix.Kernel.Frontend.headIs · body),
              numNested := match recs[0]? with | some (_, r, _) => r.motives - types.size | none => 0 },
         ctors.toList.map fun (cv, nP, nF) => { cv, nP, nF },
         recs.toList.map fun (cv, r, rules) =>
           { cv, nP := r.params, nM := r.motives, nm := r.minors, nI := r.indices, rules }⟩ = false :=
      Bool.not_eq_true _ |>.mp hwants_not
    obtain ⟨r₀, hr₀, hnd_chk⟩ := except_bind_ok_inv h
    split at hnd_chk
    · rename_i hnd_nat
      injection hnd_chk with hreq; subst hreq
      have hnd : (r₀.decls.toList.flatMap Ix.Kernel.Declaration.names).Nodup :=
        nodup_of_nodup_map cnameCode (nodup_of_nodupNat hnd_nat)
      rw [Ix.Cert.LowerDistinct.lowerInductive_ok_iff]
      refine ⟨?_, hnd⟩
      have hst_indep :
          lowerInductiveDecls st ⟨nPd, types, ctors, ctorNames, recs⟩ =
            lowerInductiveDecls ({} : State .anon) ⟨nPd, types, ctors, ctorNames, recs⟩ := by
        unfold lowerInductiveDecls
        dsimp only
        rw [hwants]
      rw [hst_indep]
      exact hr₀
    · cases hnd_chk

private def pureReadInductive1 (owner : _root_.Address) (c : Ixon.Constant)
    (ind : Ixon.Inductive) : ReadM (Read .anon) := do
  let some shape := pureBlocksLookup owner | declined "unindexed block"
  unless shape.order == #[0] do declined "non-singleton order"
  let some recRef := shape.recs[0]? | declined "no rec"
  unless shape.recs.size == 1 do declined "multi rec"
  let some entry := pureRecsLookup recRef | malformed "unindexed recursor"
  if ind.isUnsafe then declined "unsafe"
  let nPd := ind.params.toNat
  let blockLps := List.range ind.lvls.toNat
  let pself : Nat → Option (ReadM (CName .anon)) := fun i =>
    if i < 1 then some (pureMemberKey (.member owner i)) else none
  let tk ← pureMemberKey (.member owner 0)
  let tty ← pureReadExpr c id pself ind.typ
  let types : Array (CVal .anon × Nat × Nat) :=
    #[(⟨tk, List.range ind.lvls.toNat, tty⟩, ind.params.toNat, ind.indices.toNat)]
  let (ctorList, ctorNameList) ← pureReadCtorList owner c pself nPd ind.ctors.zipIdx.toList
  let recOut ← pureReadRecursor blockLps recRef entry
  pureLowerNoModel ⟨nPd, types, ctorList.toArray, #[ctorNameList], #[recOut]⟩

private theorem pureReadInductive1_sound {owner : _root_.Address} {c : Ixon.Constant}
    {ind : Ixon.Inductive} {r : Read .anon}
    (h : pureReadInductive1 owner c ind = .ok r) (st : State .anon) :
    readInductive (defCx ev) st owner c #[.indc ind] = .ok r := by
  unfold pureReadInductive1 at h
  cases hsh : pureBlocksLookup owner with
  | none => rw [hsh] at h; cases h
  | some shape =>
    rw [hsh] at h; dsimp only at h
    cases hord : (shape.order == #[0]) with
    | false => simp [hord] at h
    | true =>
      simp only [hord, ↓reduceIte] at h
      have hord_eq : shape.order = #[0] := beq_iff_eq.mp hord
      cases hr0 : shape.recs[0]? with
      | none => rw [hr0] at h; cases h
      | some recRef =>
        rw [hr0] at h; dsimp only at h
        cases hrsz : (shape.recs.size == 1) with
        | false => simp [hrsz] at h
        | true =>
          simp only [hrsz, ↓reduceIte] at h
          have hrecs_eq : shape.recs = #[recRef] := by
            have hsz1 : shape.recs.size = 1 := beq_iff_eq.mp hrsz
            cases hrc : shape.recs with
            | mk l =>
              cases l with
              | nil => rw [hrc] at hsz1; cases hsz1
              | cons x tl =>
                cases tl with
                | nil =>
                  rw [hrc] at hr0
                  simp at hr0
                  rw [hr0]
                | cons _ _ => rw [hrc] at hsz1; simp at hsz1
          cases hent : pureRecsLookup recRef with
          | none => rw [hent] at h; cases h
          | some entry =>
            rw [hent] at h; dsimp only at h
            cases hu : ind.isUnsafe with
            | true => simp [hu] at h
            | false =>
              simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨tk, htk, hr1⟩ := except_bind_ok_inv h
              obtain ⟨tty, htty, hr2⟩ := except_bind_ok_inv hr1
              obtain ⟨⟨ctorList, ctorNameList⟩, hctors, hr3⟩ := except_bind_ok_inv hr2
              obtain ⟨recOut, hrec, hlow⟩ := except_bind_ok_inv hr3
              have hsh_cx := defCx_index_blocks_of_pure ev hev_defn hsh
              have hent_cx := defCx_index_recs_of_pure ev hev_defn hent
              have htk' := pureMemberKey_sound ev hev_defn htk
              let pself : Nat → Option (ReadM (CName .anon)) := fun i =>
                if i < 1 then some (pureMemberKey (.member owner i)) else none
              let rself : Nat → Option (ReadM (CName .anon)) := fun i =>
                if i < (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).size then
                  some ((defCx ev).memberKey (.member owner i))
                else none
              have hself : ∀ i m k, pself i = some m → m = .ok k → ∃ rm, rself i = some rm ∧ rm = .ok k := by
                intro i m k hps hm
                dsimp only [pself, rself] at hps ⊢
                split at hps
                · rename_i hi
                  injection hps with hps; subst hps
                  have hi' : i < (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).size := hi
                  rw [if_pos hi']
                  exact ⟨_, rfl, pureMemberKey_sound ev hev_defn hm⟩
                · cases hps
              have htty' := pureReadExpr_sound ev hev_defn hself htty
              have hctors' := forIn_ctors_sound ev hev_defn hself ind.ctors.zipIdx.toList
                #[] [] ctorList ctorNameList hctors
              have hrec' := pureReadRecursor_sound ev hev_defn hrec
              have hlow' := pureLowerNoModel_sound hlow st
              unfold readInductive blockShapeOf
              rw [hsh_cx]
              dsimp only
              have hfilt : (shape.order.filterMap fun i =>
                  match ((#[Ixon.MutConst.indc ind] : Array Ixon.MutConst)[i]? : Option Ixon.MutConst) with
                  | some (.indc ind) => some (i, ind)
                  | _ => none) = #[(0, ind)] := by
                rw [hord_eq]; rfl
              rw [hfilt, hord_eq, hrecs_eq]
              have hsz_ok : ((#[(0, ind)] : Array (Nat × Ixon.Inductive)).size == (#[0] : Array Nat).size) = true := rfl
              have hfirst : (#[(0, ind)] : Array (Nat × Ixon.Inductive))[0]? = some (0, ind) := rfl
              have hany_u : (#[(0, ind)] : Array (Nat × Ixon.Inductive)).any (·.2.isUnsafe) = false := by
                simp [hu]
              have hall_p : (#[(0, ind)] : Array (Nat × Ixon.Inductive)).all (·.2.params.toNat == ind.params.toNat) = true := by
                simp
              rw [hsz_ok, if_pos rfl, hfirst]
              dsimp only
              rw [hany_u, if_neg (by decide), hall_p, if_pos rfl]
              dsimp only
              -- Evaluate 1-element types loop, 1-element outer ctors loop, 1-element recs loop
              have htypes_loop :
                  (forIn (#[(0, ind)] : Array (Nat × Ixon.Inductive)) (#[] : Array (CVal .anon × Nat × Nat))
                    fun (i, ind) types => do
                      pure (.yield (types.push (⟨← (defCx ev).memberKey (.member owner i),
                        List.range ind.lvls.toNat,
                        ← (MemberReader.mk' (defCx ev) c id rself).read ind.typ⟩,
                        ind.params.toNat, ind.indices.toNat)))) =
                  .ok #[(⟨tk, List.range ind.lvls.toNat, tty⟩, ind.params.toNat, ind.indices.toNat)] := by
                rw [← Array.forIn_toList]
                simp [htk', htty', bind, Except.bind, pure, Except.pure]
              have hctors_loop :
                  (forIn (#[(0, ind)] : Array (Nat × Ixon.Inductive))
                    (⟨#[], #[]⟩ : MProd (Array (CVal .anon × Nat × Nat)) (Array (List (CName .anon))))
                    fun (i, ind) acc => do
                      let r ← forIn ind.ctors.zipIdx (⟨acc.1, []⟩ : MProd (Array (CVal .anon × Nat × Nat)) (List (CName .anon)))
                        fun (ctor, j) s => do
                          unless ctor.cidx.toNat == j do malformed "constructor index differs from its position"
                          if ctor.isUnsafe then declined "unsafe inductive declaration"
                          let cv : CVal .anon :=
                            ⟨← (defCx ev).memberKey (.ctor owner i j), List.range ctor.lvls.toNat,
                              ← (MemberReader.mk' (defCx ev) c id rself).read ctor.typ⟩
                          unless ind.params.toNat + ctor.fields.toNat == piTeleLen cv.type do
                            malformed s!"constructor {cv.name} declares {ctor.fields} fields at {ind.params.toNat} parameters; its type has {piTeleLen cv.type} binders"
                          pure (.yield ⟨s.1.push (cv, ctor.params.toNat, ctor.fields.toNat), s.2 ++ [cv.name]⟩)
                      pure (.yield ⟨r.1, acc.2.push r.2⟩)) =
                  .ok ⟨ctorList.toArray, #[ctorNameList]⟩ := by
                rw [← Array.forIn_toList, List.forIn_cons, List.forIn_nil]
                dsimp only
                rw [← Array.forIn_toList, hctors']
                simp [bind, Except.bind, pure, Except.pure]
              have hrecs_loop :
                  (forIn (#[recRef] : Array (ConstRef _root_.Address))
                    (#[] : Array (CVal .anon × RecCounts × List (Ix.Kernel.RecRule .anon)))
                    fun ref recs => do
                      let some entry := (defCx ev).index.recs[ref]? | malformed "unindexed recursor"
                      pure (.yield (recs.push (← readRecursor (defCx ev) (List.range ind.lvls.toNat) ref entry)))) =
                  .ok #[recOut] := by
                rw [← Array.forIn_toList]
                simp [hent_cx, hrec', bind, Except.bind, pure, Except.pure]
              simp only [htypes_loop, hctors_loop, hrecs_loop, hlow', bind, Except.bind, pure, Except.pure]

private def pureReadRecord (owner : _root_.Address) (c : Ixon.Constant) : ReadM (Read .anon) :=
  match c.info with
  | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ =>
    if (resolveSource preStorePure owner c).isNone then
      malformed "bad proj"
    else pure {}
  | .recr _ =>
    if (pureRecsLookup (.member owner 0)).isSome then pure {}
    else declined "unindexed rec"
  | .axio a => do
    if a.isUnsafe then declined "unsafe axiom"
    let ck ← pureMemberKey (.member owner 0)
    let ty ← pureReadExpr c id (fun _ => none) a.typ
    pure { decls := #[Ix.Kernel.Declaration.axiomDecl ⟨ck, List.range a.lvls.toNat, ty⟩] }
  | .quot q => do
    let ck ← pureMemberKey (.member owner 0)
    let ty ← pureReadExpr c id (fun _ => none) q.typ
    let kind : Ix.Kernel.QuotKind := match q.kind with
      | .type => .type | .ctor => .ctor | .lift => .lift | .ind => .ind
    pure { decls := #[Ix.Kernel.Declaration.quotDecl kind ⟨ck, List.range q.lvls.toNat, ty⟩] }
  | .muts ms =>
    match ms.toList with
    | [.indc ind] => pureReadInductive1 owner c ind
    | _ => declined "unsupported muts in prelude"
  | .defn _ => declined "unexpected defn in prelude"

private theorem pureReadRecord_sound {owner : _root_.Address} {c : Ixon.Constant}
    (hc : (owner, c) ∈ committedPreludeList) {r : Read .anon}
    (h : pureReadRecord owner c = .ok r) (st : State .anon) :
    readRecord (defCx ev) st owner c = .ok r := by
  unfold pureReadRecord at h
  unfold readRecord
  have hself_none : ∀ i (m : ReadM (CName .anon)) k,
      (fun _ : Nat => (none : Option (ReadM (CName .anon)))) i = some m → m = .ok k →
      ∃ rm, (fun _ : Nat => (none : Option (ReadM (CName .anon)))) i = some rm ∧ rm = .ok k :=
    fun _ _ _ hn => nomatch hn
  cases hci : c.info with
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    rw [hci] at h ⊢
    rw [resolveSource_defCx_eq_pure ev hc]
    exact h
  | recr rc =>
    rw [hci] at h ⊢
    cases hp : pureRecsLookup (.member owner 0) with
    | none => rw [hp] at h; cases h
    | some entry =>
      rw [hp] at h
      injection h with hr; subst hr
      have hcx_rec := defCx_index_recs_of_pure ev hev_defn hp
      have hcont : (defCx ev).index.recs.contains (.member owner 0) = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, hcx_rec]; rfl
      simp [hcont, pure, Except.pure]
  | axio a =>
    rw [hci] at h ⊢
    cases hu : a.isUnsafe with
    | true => simp [hu] at h
    | false =>
      simp only [hu, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨ck, hck, hr1⟩ := except_bind_ok_inv h
      obtain ⟨ty, hty, hpure⟩ := except_bind_ok_inv hr1
      injection hpure with hr; subst hr
      have hck' := pureMemberKey_sound ev hev_defn hck
      have hty' := pureReadExpr_sound ev hev_defn hself_none hty
      simp [hck', hty', bind, Except.bind, pure, Except.pure]
  | quot q =>
    rw [hci] at h ⊢
    obtain ⟨ck, hck, hr1⟩ := except_bind_ok_inv h
    obtain ⟨ty, hty, hpure⟩ := except_bind_ok_inv hr1
    injection hpure with hr; subst hr
    have hck' := pureMemberKey_sound ev hev_defn hck
    have hty' := pureReadExpr_sound ev hev_defn hself_none hty
    simp [hck', hty', bind, Except.bind, pure, Except.pure]
  | muts ms =>
    rw [hci] at h ⊢
    cases hms : ms.toList with
    | nil => rw [hms] at h; cases h
    | cons m0 tl =>
      cases tl with
      | cons _ _ => rw [hms] at h; cases h
      | nil =>
        cases m0 with
        | defn _ | recr _ => rw [hms] at h; cases h
        | indc ind =>
          rw [hms] at h
          have harr : ms = #[.indc ind] := by
            apply Array.ext'; exact hms
          subst harr
          have hany_i : (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).any
              (fun | .indc _ => true | _ => false) = true := rfl
          have hany_d : (#[Ixon.MutConst.indc ind] : Array Ixon.MutConst).any
              (fun | .defn _ => true | _ => false) = false := rfl
          rw [hany_i, if_pos rfl, hany_d, if_neg (by decide)]
          exact pureReadInductive1_sound ev hev_defn h st
  | defn _ => rw [hci] at h; cases h

private def pureReadStream :
    List (_root_.Address × Ixon.Constant) → ReadM (Array (CDecl .anon))
  | [] => pure #[]
  | (a, c) :: rest => do
    let r ← pureReadRecord a c
    let tail ← pureReadStream rest
    pure (r.decls ++ tail)

private theorem pureReadStream_sound :
    ∀ (rs : List (_root_.Address × Ixon.Constant)) {out : Array (CDecl .anon)},
      (∀ p ∈ rs, p ∈ committedPreludeList) →
      pureReadStream rs = .ok out →
      ∀ st : State .anon, ∃ st', StreamRead (defCx ev) st rs st' out
  | [], _, _, h, st => by
    injection h with ho; subst ho
    exact ⟨st, .nil⟩
  | (a, c) :: rest, _, hsub, h, st => by
    unfold pureReadStream at h
    obtain ⟨r, hr, hrest⟩ := except_bind_ok_inv h
    obtain ⟨tail, htail, hpure⟩ := except_bind_ok_inv hrest
    injection hpure with ho; subst ho
    have hr' := pureReadRecord_sound ev hev_defn (hsub (a, c) List.mem_cons_self) hr st
    obtain ⟨st', hst'⟩ := pureReadStream_sound rest
      (fun p hp => hsub p (List.mem_cons_of_mem _ hp)) htail (st.commit r)
    exact ⟨st', .cons hr' hst'⟩

end WithEv

private def purePreludeCheckBool : Bool :=
  match pureReadStream committedPreludeList with
  | .ok decls =>
    (decls.toList.map (·.names) ==
      Ix.Kernel.preludeShape.map (·.map (Ix.Kernel.Key.role (md := .anon)))) &&
    committedPrelude.all (fun p => fallbackRecursorShape p.2)
  | .error _ => false

private theorem purePreludeCheck_ok : purePreludeCheckBool = true := by
  decide +kernel

/-- The committed prelude succeeds under `committedDefaultRoleTable` in `.anon` mode. -/
theorem preludeFor_defaultRoleTable :
    ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) committedDefaultRoleTable = .ok pre := by
  have hchk := purePreludeCheck_ok
  unfold purePreludeCheckBool at hchk
  cases hps : pureReadStream committedPreludeList with
  | error _ => rw [hps] at hchk; cases hchk
  | ok decls =>
    rw [hps, Bool.and_eq_true] at hchk
    obtain ⟨hshape, hrec_pre⟩ := hchk
    obtain ⟨ev, hev_eq, hev_addrs, hev_defn⟩ := evidenceRecords_spec
    obtain ⟨st', hstream⟩ :=
      pureReadStream_sound ev hev_defn committedPreludeList (fun _ h => h) hps {}
    have hrr := Ix.Cert.Stream.readRecords_complete hstream committedPreAddrs_nodup
    have hread : preludeRead (md := .anon) committedDefaultRoleTable =
        .ok ⟨committedPrelude, ev, committedBlobs, ⟨decls⟩, st'⟩ := by
      unfold preludeRead readPrelude
      rw [preludeRecords_eq, hev_eq, evidenceBlobs_eq]
      simp only [bind, Except.bind, pure, Except.pure]
      change (match readRecords (defCx ev) {} committedPreludeList.toArray with
        | .ok (state, decls) => Except.ok ⟨committedPrelude, ev, committedBlobs, ⟨decls⟩, state⟩
        | .error (e, i) => throw s!"prelude record {i}: {e}") = _
      rw [hrr]
    have hcs : checkPreludeShape (md := .anon)
        ⟨committedPrelude, ev, committedBlobs, ⟨decls⟩, st'⟩ = .ok () := by
      unfold checkPreludeShape
      dsimp only
      rw [hshape, if_pos rfl]
      rfl
    have hcfr : checkFallbackRecursors (md := .anon)
        ⟨committedPrelude, ev, committedBlobs, ⟨decls⟩, st'⟩ = .ok () := by
      unfold checkFallbackRecursors
      dsimp only
      have hall : (committedPrelude ++ ev).all (fun p => fallbackRecursorShape p.2) = true := by
        rw [Array.all_eq_true_iff_forall_mem]
        intro p hp
        rcases Array.mem_append.mp hp with h1 | h2
        · exact Array.all_eq_true_iff_forall_mem.mp hrec_pre p h1
        · obtain ⟨d, hd⟩ := hev_defn p (Array.mem_toList_iff.mpr h2)
          simp [fallbackRecursorShape, hd]
      rw [hall, if_pos rfl]
      rfl
    refine ⟨⟨committedPrelude, ev, committedBlobs, ⟨decls⟩, st'⟩, ?_⟩
    unfold preludeFor
    rw [hread]
    simp only [bind, Except.bind, pure, Except.pure, hcs, hcfr]

/-! ## `ReaderTable` consequences: `preludeFor` and `LiteralSupportBound` -/

/-- Under `ReaderTable clm V b` and `admitBinding Address.admissionHash b = .ok t`,
`preludeFor (md := .anon) t` succeeds. -/
theorem preludeFor_of_readerTable {clm : Ix.Claim} {V : View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable}
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) t = .ok pre := by
  rcases hrt.2 with hdef | htab
  · have ht := Ix.Cert.ReadingKeys.admitBinding_default defaultTable_eq hdef hadm
    subst ht
    exact preludeFor_defaultRoleTable
  · obtain ⟨t', hadm', _, hacc⟩ := htab
    rw [hadm] at hadm'
    injection hadm' with ht_eq
    subst ht_eq
    obtain ⟨_, _, _, _, -, -, t'', pre, _, _, hadm'', -, -, hpre, -⟩ := hacc
    rw [hadm] at hadm''
    injection hadm'' with ht_eq'
    subst ht_eq'
    exact ⟨pre, hpre⟩

/-- Under `ReaderTable clm V b` and `admitBinding Address.admissionHash b = .ok t`,
`LiteralSupportBound t` holds. -/
theorem literalSupportBound_of_readerTable {clm : Ix.Claim} {V : View}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    (hrt : IxVM.Consistency.ReaderTable clm V b)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t) :
    IxVM.Refinement.LiteralSupportBound t := by
  rcases hrt.2 with hdef | htab
  · have ht := Ix.Cert.ReadingKeys.admitBinding_default defaultTable_eq hdef hadm
    subst ht
    exact committedDefaultRoleTable_literalSupportBound
  · obtain ⟨t', hadm', hlit, _⟩ := htab
    rw [hadm] at hadm'
    injection hadm' with ht_eq
    subst ht_eq
    exact hlit

/-! ## Collision-free agreement between `committedImages` / `pre` fallback and `LoadedBy calls E₀` -/

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
  cases readRecords (contextOf t recs [] evs blobs) {} recs with
  | error _ => simp [throw, throwThe, MonadExceptOf.throw] at hr3
  | ok pair =>
    injection hr3 with hp
    cases hp
    exact hblobs

private theorem evidenceBlobs_rows :
    ∀ {rows : List (String × String)} {out : List (_root_.Address × ByteArray)},
      (rows.mapM fun (hex, bytes) => do
        let some a := addressOfHex hex | throw s!"evidence blob: bad address {hex}"
        let some b := bytesOfHex bytes | throw s!"evidence blob: bad bytes at {hex}"
        pure (a, b)) = .ok out →
      ∀ p ∈ out, ∃ row ∈ rows, addressOfHex row.1 = some p.1 ∧ bytesOfHex row.2 = some p.2
  | [], _, h, p, hp => by
    injection h with ho; subst ho; cases hp
  | (hex, bytes) :: rs, out, h, p, hp => by
    rw [List.mapM_cons] at h
    cases ha : addressOfHex hex with
    | none => simp [ha, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | some a =>
      simp only [ha, bind, Except.bind] at h
      cases hb : bytesOfHex bytes with
      | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      | some b =>
        simp only [hb, pure, Except.pure] at h
        cases htl : (rs.mapM fun (hex, bytes) => do
            let some a := addressOfHex hex | throw s!"evidence blob: bad address {hex}"
            let some b := bytesOfHex bytes | throw s!"evidence blob: bad bytes at {hex}"
            pure (a, b)) with
        | error _ => rw [htl] at h; cases h
        | ok tail =>
          rw [htl] at h
          injection h with ho; subst ho
          rcases List.mem_cons.mp hp with rfl | hmem
          · exact ⟨(hex, bytes), List.mem_cons_self, ha, hb⟩
          · obtain ⟨row, hr, ha', hb'⟩ := evidenceBlobs_rows htl p hmem
            exact ⟨row, List.mem_cons_of_mem _ hr, ha', hb'⟩

theorem blob_mem_committedImages_of_fallback {md : Ix.Kernel.Mode}
    {t : Ix.Kernel.RoleTable} {pre : Prelude md}
    (hpre : preludeFor t = .ok pre) {a : _root_.Address} {blob : ByteArray}
    (hmem : (a, blob) ∈ pre.blobs) :
    blob ∈ IxVM.Consistency.committedImages ∧ Address.blake3Pure blob = a := by
  have heb := preludeFor_blobs hpre
  unfold evidenceBlobs at heb
  obtain ⟨row, hrow, ha, hb⟩ := evidenceBlobs_rows heb (a, blob) hmem
  have hhash := blobsHashed row hrow
  rw [hb, ha, Option.map_some, Option.some.injEq, Address.admissionHash_eq] at hhash
  refine ⟨?_, hhash⟩
  unfold IxVM.Consistency.committedImages
  rw [List.mem_filterMap]
  refine ⟨row.2, ?_, hb⟩
  rw [List.mem_map]
  refine ⟨row, ?_, rfl⟩
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
  ·exact .inl (.inl ⟨Address.blake3Pure img, img, bytes,
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
    rw [hraw, Ixon.Verify.BoundedConstant.deConstantExact_serConstant c hwf] at hexact
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
