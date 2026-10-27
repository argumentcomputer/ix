import Ix.Cert.CtxAgree
import Ix.Cert.PreludeAgree
import Ix.Cert.PrepareRename
import IxC.Kernel.Verify.Rename.UnionFold

/-! # Reader states under a renaming

The reader of a compiled closure and quotient Source both thread a reader state through
their reads (`State.commit`). This module relates two such states under a renaming of
input names, on a scope where the renaming is injective (`StateRen`):

* a read that declares renamed declarations, and generates, owns and records nothing,
  keeps the relation (`StateRen.commit_plain`); a read that changes no entry keeps it on
  either side (`StateRen.commit_inert_left`, `StateRen.commit_inert_right`);
* the prelude states of the two readings of the committed prelude are related under every
  renaming (`StateRen.of_prelude`);
* related final states keep related prelude states' entries whenever the Source one does
  (`keepsPrelude_ren`). -/

namespace Ix.Cert.StreamRename

open Ix.Kernel
open Ix.Kernel.Reader (State Read CDecl CName CExpr)
open Ix.Kernel.Frontend (ProjRecOwner)
open Ix.Kernel.Frontend.InModel (BlockRec)
open Ix.Cert.CtxAgree (Entry noteEntries insOpt tyOf htOf renE)

variable {md md' : Mode}

/-- **Two reader states agree under `f` on the scope `P`**: at every good key, the renamed
entries of every field. -/
structure StateRen (f : md.Id → md'.Id) (P : KeyScope md) (stS : State md) (stA : State md') :
    Prop where
  types : ∀ k : Key md, k.Good P →
    stA.constTypes[k.map f]? = (stS.constTypes[k]?).map fun v => (v.1, v.2.mapKeys f)
  heights : ∀ k : Key md, k.Good P → stA.heights[k.map f]? = stS.heights[k]?
  blocks : ∀ k : Key md, k.Good P →
    stA.indBlocks[k.map f]? = (stS.indBlocks[k]?).map (BlockRec.mapKeys f)
  owners : ∀ k : Key md, k.Good P →
    stA.projOwners[k.map f]? = (stS.projOwners[k]?).map (ProjRecOwner.mapKeys f)
  levels : ∀ k : Key md, k.Good P → stA.projLevels[k.map f]? = stS.projLevels[k]?

/-- The two prelude states are related on every scope. -/
theorem StateRen.of_prelude {f : Mode.Id .source → Mode.Id .anon} {P : KeyScope .source}
    {stS : State .source} {stA : State .anon} (h : PreludeAgree.StateRen f stS stA) :
    StateRen f P stS stA :=
  ⟨fun k _ => h.types k, fun k _ => h.heights k, fun k _ => h.blocks k, fun k _ => h.owners k,
    fun k _ => h.levels k⟩

/-! ## The prelude's entries -/

/-- A key a field holds an entry at is one of the state's keys. -/
theorem mem_keys_of {st : State md} {k : CName md} :
    (st.constTypes[k]?.isSome ∨ st.heights[k]?.isSome ∨ st.indBlocks[k]?.isSome ∨
      st.projOwners[k]?.isSome ∨ st.projLevels[k]?.isSome) → k ∈ st.keys := by
  intro h
  simp only [State.keys, List.mem_append, Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains, or_assoc]
  simp only [Std.HashMap.isSome_getElem?_eq_contains] at h
  rcases h with h | h | h | h | h <;> simp [h]

/-- **Related final states keep related prelude states' entries** whenever the Source
one does. -/
theorem keepsPrelude_ren {f : Mode.Id .source → Mode.Id .anon} {P : KeyScope .source}
    {s0 s1 : State .source} {a0 a1 : State .anon} (h0 : PreludeAgree.StateRen f s0 a0)
    (hP : ∀ k ∈ s0.keys, k.Good P) (h1 : StateRen f P s1 a1)
    (hk : State.keepsPrelude s0 s1 = true) : State.keepsPrelude a0 a1 = true := by
  rw [State.keepsPrelude_iff] at hk ⊢
  intro kA hkA
  -- every key of the renamed prelude state is a renamed key of the prelude state
  have hsome : a0.constTypes[kA]?.isSome ∨ a0.heights[kA]?.isSome ∨ a0.indBlocks[kA]?.isSome ∨
      a0.projOwners[kA]?.isSome ∨ a0.projLevels[kA]?.isSome := by
    simp only [State.keys, List.mem_append, Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains,
      or_assoc] at hkA
    simp only [Std.HashMap.isSome_getElem?_eq_contains]
    exact hkA
  have hrep : ∃ k : Key .source, kA = k.map f ∧ k ∈ s0.keys := by
    rcases hsome with h | h | h | h | h
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨k, rfl⟩ := h0.typesOnly _ b hb
      refine ⟨k, rfl, mem_keys_of (.inl ?_)⟩
      have := h0.types k
      rw [hb] at this
      cases hs : s0.constTypes[k]? <;> simp_all
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨k, rfl⟩ := h0.heightsOnly _ b hb
      refine ⟨k, rfl, mem_keys_of (.inr (.inl ?_))⟩
      rw [← h0.heights k, hb]; rfl
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨k, rfl⟩ := h0.blocksOnly _ b hb
      refine ⟨k, rfl, mem_keys_of (.inr (.inr (.inl ?_)))⟩
      have := h0.blocks k
      rw [hb] at this
      cases hs : s0.indBlocks[k]? <;> simp_all
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨k, rfl⟩ := h0.ownersOnly _ b hb
      refine ⟨k, rfl, mem_keys_of (.inr (.inr (.inr (.inl ?_))))⟩
      have := h0.owners k
      rw [hb] at this
      cases hs : s0.projOwners[k]? <;> simp_all
    · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨k, rfl⟩ := h0.levelsOnly _ b hb
      refine ⟨k, rfl, mem_keys_of (.inr (.inr (.inr (.inr ?_))))⟩
      rw [← h0.levels k, hb]; rfl
  obtain ⟨k, rfl, hk0⟩ := hrep
  obtain ⟨e1, e2, e3, e4, e5⟩ := hk k hk0
  have hg := hP k hk0
  exact ⟨by rw [h1.types k hg, e1, h0.types k], by rw [h1.heights k hg, e2, h0.heights k],
    by rw [h1.blocks k hg, e3, h0.blocks k], by rw [h1.owners k hg, e4, h0.owners k],
    by rw [h1.levels k hg, e5, h0.levels k]⟩

/-! ## Reads that change the state alike -/

/-- A read that generates, owns and records nothing: a definition's, an axiom's or a
quotient constant's. -/
structure Plain (r : Read md) : Prop where
  generated : r.generated = 0
  owners : r.owners = []
  blocks : r.blocks = []

theorem note_projOwners (st : State md) (d : CDecl md) : (st.note d).projOwners = st.projOwners := by
  cases d <;> (refine CtxAgree.foldl_keep State.projOwners _ (fun s e => ?_) _ _; rfl)

theorem note_projLevels (st : State md) (d : CDecl md) : (st.note d).projLevels = st.projLevels := by
  cases d <;> (refine CtxAgree.foldl_keep State.projLevels _ (fun s e => ?_) _ _; rfl)

theorem commit_projOwners_plain (st : State md) {r : Read md} (h : Plain r) :
    (st.commit r).projOwners = st.projOwners := by
  rw [CtxAgree.commit_eq]
  simp only [h.owners, h.blocks, h.generated, Nat.not_lt_zero, ite_false, List.foldl_nil]
  exact CtxAgree.foldl_keep State.projOwners _ (fun s (x : CDecl md × Nat) => note_projOwners s x.1) _ _

theorem commit_projLevels_plain (st : State md) {r : Read md} (h : Plain r) :
    (st.commit r).projLevels = st.projLevels := by
  rw [CtxAgree.commit_eq]
  simp only [h.owners, h.blocks, h.generated, Nat.not_lt_zero, ite_false, List.foldl_nil]
  exact CtxAgree.foldl_keep State.projLevels _ (fun s (x : CDecl md × Nat) => note_projLevels s x.1) _ _

/-- Inserts at renamed good keys keep the renamed entries. -/
theorem foldl_insOpt_ren {γ γ' β β' : Type} {f : md.Id → md'.Id} {P : KeyScope md}
    (hf : InjOn f P) (g : γ → Option (Key md × β)) (g' : γ' → Option (Key md' × β'))
    (ρ : γ → γ') (ψ : β → β') (hg : ∀ e, g' (ρ e) = (g e).map fun p => (p.1.map f, ψ p.2)) :
    ∀ (l : List γ), (∀ e ∈ l, ∀ p, g e = some p → p.1.Good P) →
      ∀ (m : Std.HashMap (Key md) β) (m' : Std.HashMap (Key md') β'),
        (∀ k : Key md, k.Good P → m'[k.map f]? = (m[k]?).map ψ) →
        ∀ k : Key md, k.Good P →
          ((l.map ρ).foldl (insOpt g') m')[k.map f]? = ((l.foldl (insOpt g) m)[k]?).map ψ
  | [], _, _, _, hm => hm
  | e :: l, hl, m, m', hm => by
    simp only [List.map_cons, List.foldl_cons]
    refine foldl_insOpt_ren hf g g' ρ ψ hg l (fun e' he' => hl e' (List.mem_cons_of_mem _ he'))
      _ _ ?_
    intro k hk
    unfold insOpt
    rw [hg e]
    cases he : g e with
    | none => exact hm k hk
    | some p =>
      obtain ⟨a, b⟩ := p
      have ha : a.Good P := hl e List.mem_cons_self _ he
      simp only [Option.map_some, Std.HashMap.getElem?_insert]
      by_cases hak : a = k
      · subst hak; simp
      · have hne : a.map f ≠ k.map f := fun h => hak (Key.map_inj hf ha hk h)
        simp only [beq_iff_eq, hne, hak, ite_false]
        exact hm k hk

/-- **A plain read and its renaming keep two related states related**: the renamed read
declares the read's declarations renamed, every name they declare is good, and none is
a basis declaration. -/
theorem StateRen.commit_plain {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {stS : State md} {stA : State md'} (h : StateRen f P stS stA) {rS : Read md} {rA : Read md'}
    (pS : Plain rS) (pA : Plain rA) (hdecls : rA.decls = rS.decls.map (Declaration.mapKeys f))
    (hbasis : ∀ d ∈ rS.decls.toList, ∀ k, d ≠ .basisDecl k)
    (hgood : ∀ d ∈ rS.decls.toList, ∀ e ∈ noteEntries d, e.1.Good P) :
    StateRen f P (stS.commit rS) (stA.commit rA) := by
  have hentries : rA.decls.toList.flatMap noteEntries =
      (rS.decls.toList.flatMap noteEntries).map (renE f) := by
    rw [hdecls, Array.toList_map, List.flatMap_map, List.map_flatMap]
    exact CtxAgree.flatMap_congr' fun d hd => CtxAgree.noteEntries_mapKeys (hbasis d hd)
  have hkeys : ∀ e ∈ rS.decls.toList.flatMap noteEntries, e.1.Good P := by
    intro e he
    obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
    exact hgood d hd e he
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [CtxAgree.commit_constTypes, CtxAgree.commit_constTypes, hentries]
    exact foldl_insOpt_ren hf tyOf tyOf (renE f) (fun v => (v.1, v.2.mapKeys f))
      (fun e => rfl) _ (fun e he p hp => by
        have := CtxAgree.tyOf_renE (f := f) e
        unfold tyOf at hp; cases hp; exact hkeys e he)
      _ _ h.types k hk
  · rw [CtxAgree.commit_heights, CtxAgree.commit_heights, hentries]
    have := foldl_insOpt_ren hf htOf htOf (renE f) (fun v : Nat => v)
      (fun e => by rw [CtxAgree.htOf_renE]) _
      (fun e he p hp => by rw [← CtxAgree.htOf_name hp]; exact hkeys e he)
      stS.heights stA.heights (fun k hk => by rw [h.heights k hk, Option.map_id']) k hk
    rw [this, Option.map_id']
  · rw [CtxAgree.commit_indBlocks, CtxAgree.commit_indBlocks, pS.blocks, pA.blocks]
    exact h.blocks k hk
  · rw [commit_projOwners_plain _ pS, commit_projOwners_plain _ pA]
    exact h.owners k hk
  · rw [commit_projLevels_plain _ pS, commit_projLevels_plain _ pA]
    exact h.levels k hk

/-- A read that declares nothing changes no entry. -/
structure Inert (r : Read md) : Prop extends Plain r where
  decls : r.decls = #[]

theorem commit_inert_fields (st : State md) {r : Read md} (h : Inert r) :
    (st.commit r).constTypes = st.constTypes ∧ (st.commit r).heights = st.heights ∧
      (st.commit r).indBlocks = st.indBlocks ∧ (st.commit r).projOwners = st.projOwners ∧
      (st.commit r).projLevels = st.projLevels := by
  refine ⟨?_, ?_, ?_, commit_projOwners_plain st h.toPlain, commit_projLevels_plain st h.toPlain⟩
  · rw [CtxAgree.commit_constTypes, h.decls]; rfl
  · rw [CtxAgree.commit_heights, h.decls]; rfl
  · rw [CtxAgree.commit_indBlocks, h.blocks]; rfl

theorem StateRen.commit_inert_left {f : md.Id → md'.Id} {P : KeyScope md} {stS : State md}
    {stA : State md'} (h : StateRen f P stS stA) {r : Read md} (hr : Inert r) :
    StateRen f P (stS.commit r) stA := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := commit_inert_fields stS hr
  exact ⟨fun k hk => e1 ▸ h.types k hk, fun k hk => e2 ▸ h.heights k hk,
    fun k hk => e3 ▸ h.blocks k hk, fun k hk => e4 ▸ h.owners k hk, fun k hk => e5 ▸ h.levels k hk⟩

theorem StateRen.commit_inert_right {f : md.Id → md'.Id} {P : KeyScope md} {stS : State md}
    {stA : State md'} (h : StateRen f P stS stA) {r : Read md'} (hr : Inert r) :
    StateRen f P stS (stA.commit r) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := commit_inert_fields stA hr
  exact ⟨fun k hk => e1 ▸ h.types k hk, fun k hk => e2 ▸ h.heights k hk,
    fun k hk => e3 ▸ h.blocks k hk, fun k hk => e4 ▸ h.owners k hk, fun k hk => e5 ▸ h.levels k hk⟩

/-! ## The committed prelude's states -/

/-- A field that agrees, names erased, holds entries only at keys naming no input. -/
theorem fieldAgree_keys {α β : Type} [BEq β] {mS : Std.HashMap (Key .source) α}
    {mA : Std.HashMap (Key .anon) β} {ok : α → Bool} {erase : α → β}
    (h : PreludeAgree.fieldAgreeB mS mA ok erase = true) {k : Key .source} (hk : mS[k]?.isSome) :
    k.Good PreludeAgree.NoIds := by
  simp only [PreludeAgree.fieldAgreeB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
  have hkv := h.1 (k, v) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hv)
  exact Ix.LeanIngress.Key.goodB_spec hkv.1.1

/-- The committed prelude's Source state names no input. -/
theorem preludeAgree_keys {preS : Ix.Kernel.Reader.Prelude .source}
    {preA : Ix.Kernel.Reader.Prelude .anon} (h : PreludeAgree.preludeAgreeB preS preA = true) :
    ∀ k ∈ preS.state.keys, k.Good PreludeAgree.NoIds := by
  simp only [PreludeAgree.preludeAgreeB, PreludeAgree.stateAgreeB, Bool.and_eq_true] at h
  obtain ⟨-, ⟨⟨⟨⟨hT, hH⟩, hB⟩, hO⟩, hL⟩⟩ := h
  intro k hk
  simp only [State.keys, List.mem_append, Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains,
    or_assoc] at hk
  simp only [← Std.HashMap.isSome_getElem?_eq_contains] at hk
  rcases hk with hk | hk | hk | hk | hk
  · exact fieldAgree_keys hT hk
  · exact fieldAgree_keys hH hk
  · exact fieldAgree_keys hB hk
  · exact fieldAgree_keys hO hk
  · exact fieldAgree_keys hL hk

/-- **The reader keeps the committed prelude's entries whenever quotient Source does**, at
final states related on a scope of input names. -/
theorem keepsPrelude_of_agree {preS : Ix.Kernel.Reader.Prelude .source}
    {preA : Ix.Kernel.Reader.Prelude .anon} (h : PreludeAgree.preludeAgreeB preS preA = true)
    {f : Mode.Id .source → Mode.Id .anon} {Q : Mode.Id .source → Prop} {s1 : State .source}
    {a1 : State .anon} (h1 : StateRen f (KeyScope.ofId Q) s1 a1)
    (hk : State.keepsPrelude preS.state s1 = true) : State.keepsPrelude preA.state a1 = true :=
  keepsPrelude_ren (PreludeAgree.preludeAgree_state h f)
    (fun k hk => Key.Good.mono
      (fun i hi => absurd (show PreludeAgree.noId i = true from hi) (by simp [PreludeAgree.noId]))
      (fun _ _ => trivial) (preludeAgree_keys h k hk)) h1 hk

/-! ## Streams of plain reads -/

/-- **The reader's records against quotient Source's reads, unit by unit**, from the Source
state `stS`: a Source read that changes no entry has no record; any other is plain, declares
good names and no basis declaration, and has one record, which every reader state related
to `stS` reads as a plain read declaring its declarations renamed. -/
inductive PlainUnits (f : md.Id → md'.Id) (P : KeyScope md) (cx : Ix.Kernel.Reader.Ctx md') :
    State md → List (Read md) → List (Address × Ixon.Constant) → Prop where
  | nil {stS : State md} : PlainUnits f P cx stS [] []
  | inert {stS : State md} {rS : Read md} {rs : List (Read md)} {R : List (Address × Ixon.Constant)}
      (hr : Inert rS) (tail : PlainUnits f P cx (stS.commit rS) rs R) :
      PlainUnits f P cx stS (rS :: rs) R
  | record {stS : State md} {rS : Read md} {rs : List (Read md)} {a : Address} {c : Ixon.Constant}
      {R : List (Address × Ixon.Constant)} (plain : Plain rS)
      (hbasis : ∀ d ∈ rS.decls.toList, ∀ k, d ≠ .basisDecl k)
      (hgood : ∀ d ∈ rS.decls.toList, ∀ e ∈ noteEntries d, e.1.Good P)
      (reads : ∀ stA : State md', StateRen f P stS stA →
        ∃ rA, Ix.Kernel.Reader.readRecord cx stA a c = .ok rA ∧ Plain rA ∧
          rA.decls = rS.decls.map (Declaration.mapKeys f))
      (tail : PlainUnits f P cx (stS.commit rS) rs R) :
      PlainUnits f P cx stS (rS :: rs) ((a, c) :: R)

/-- **The reader reads plain units as quotient Source's reads renamed**: from related
states, it reads the records to the Source declarations renamed, and ends related to the
Source state. -/
theorem PlainUnits.streamRead {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {cx : Ix.Kernel.Reader.Ctx md'} {stS : State md} {rs : List (Read md)}
    {R : List (Address × Ixon.Constant)} (h : PlainUnits f P cx stS rs R) :
    ∀ {stA : State md'}, StateRen f P stS stA →
      ∃ stA' out, Ix.Kernel.Reader.StreamRead cx stA R stA' out ∧
        out.toList = (rs.flatMap (·.decls.toList)).map (Declaration.mapKeys f) ∧
        StateRen f P (rs.foldl State.commit stS) stA' := by
  induction h with
  | nil => intro stA hst; exact ⟨stA, #[], .nil, rfl, hst⟩
  | inert hr _ ih =>
    intro stA hst
    obtain ⟨stA', out, hread, hout, hfin⟩ := ih (hst.commit_inert_left hr)
    refine ⟨stA', out, hread, ?_, hfin⟩
    rw [hout, List.flatMap_cons, hr.decls]
    rfl
  | record plain hbasis hgood reads _ ih =>
    intro stA hst
    obtain ⟨rA, hrA, pA, hdecls⟩ := reads stA hst
    obtain ⟨stA', out, hread, hout, hfin⟩ :=
      ih (hst.commit_plain hf plain pA hdecls hbasis hgood)
    refine ⟨stA', rA.decls ++ out, .cons hrA hread, ?_, hfin⟩
    rw [Array.toList_append, hout, hdecls, Array.toList_map, List.flatMap_cons, List.map_append]

/-! ## The conclusion for plain units -/

/-- The committed prelude's Source declarations name no input. -/
theorem preludeAgree_declsGood {preS : Ix.Kernel.Reader.Prelude .source}
    {preA : Ix.Kernel.Reader.Prelude .anon} (h : PreludeAgree.preludeAgreeB preS preA = true) :
    ∀ p ∈ preS.ix.decls, p.Good PrepareRename.NoInput := by
  simp only [PreludeAgree.preludeAgreeB, Bool.and_eq_true] at h
  intro p hp
  refine Declaration.Good.mono ⟨fun i hi => ?_, fun _ _ => trivial⟩
    (Ix.LeanIngress.declsGoodB_good h.1.1 p hp)
  exact absurd (show PreludeAgree.noId i = true from hi) (by simp [PreludeAgree.noId])

/-- **A closure read unit by unit as plain units concludes as the reader's streams ask**:
from the anonymous prelude state the reader reads the records, keeps the prelude's entries,
and its prepared declarations are quotient Source's prepared declarations renamed; given the
committed prelude's agreement at both modes, quotient Source's lowering of the units (its
declarations, good on a scope where the renaming is injective) and its keeping the prelude. -/
theorem plainUnits_conclusion {f : Mode.Id .source → Mode.Id .anon} {Q : Mode.Id .source → Prop}
    (hf : InjOn f Q) {pre : Ix.Kernel.Reader.Prelude .source} {preA : Ix.Kernel.Reader.Prelude .anon}
    (hPA : PreludeAgree.preludeAgreeB pre preA = true) {cx : Ix.Kernel.Reader.Ctx .anon}
    {rs : List (Read .source)} {R : List (Address × Ixon.Constant)}
    (units : PlainUnits f (KeyScope.ofId Q) cx pre.state rs R) {decls : Array (CDecl .source)}
    (hdecls : decls.toList = rs.flatMap (·.decls.toList)) (hgood : ∀ d ∈ decls, d.Good Q)
    (hkeep : State.keepsPrelude pre.state (rs.foldl State.commit pre.state) = true) :
    ∃ st' declsA, Ix.Kernel.Reader.StreamRead cx preA.state R st' declsA ∧
      State.keepsPrelude preA.state st' = true ∧
      (Frontend.preparePrelude preA.ix declsA).toList =
        (Frontend.preparePrelude pre.ix decls).toList.map (Declaration.mapKeys f) := by
  have h0 := StateRen.of_prelude (P := KeyScope.ofId Q) (PreludeAgree.preludeAgree_state hPA f)
  obtain ⟨st', out, hread, hout, hfin⟩ := units.streamRead hf h0
  refine ⟨st', out, hread, keepsPrelude_of_agree hPA hfin hkeep, ?_⟩
  have hout' : out = decls.map (Declaration.mapKeys f) :=
    Array.ext' (by rw [hout, Array.toList_map, hdecls])
  rw [hout', PrepareRename.preparePrelude_mapKeys hf (PreludeAgree.preludeAgree_decls hPA f)
    (preludeAgree_declsGood hPA) hgood, Array.toList_map]

/--
info: 'Ix.Cert.StreamRename.plainUnits_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms plainUnits_conclusion

end Ix.Cert.StreamRename
