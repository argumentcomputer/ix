import Ix.Cert.StreamRename
import Ix.Cert.CtxAgreeProjFields

/-! # Streams of renamed units

`StreamRename` relates the two reader states under a renaming and reads a closure unit by
unit when every unit is plain. This module drops the restriction: a read whose declarations,
generated count, owners and blocks are its Source partner's renamed keeps two related states
related (`StateRen.commit`), so a closure whose records match quotient Source's reads unit by
unit (`Units`: a Source read that changes nothing has no record, a record that reads to
nothing has no Source read, and every other record reads, from any related state, as its
unit renamed) reads as Source's declarations renamed (`Units.streamRead`), and the reader's
streams conclude as they ask (`units_conclusion`). Inductive blocks are such units: the
block record reads as the block's lowering, its projection records read to nothing. -/

namespace Ix.Cert.StreamUnits

open Ix.Kernel
open Ix.Kernel.Reader (State Read CDecl CName)
open Ix.Kernel.Frontend (ProjRecOwner)
open Ix.Kernel.Frontend.InModel (BlockRec)
open Ix.Cert.CtxAgree (noteEntries tyOf htOf renE UnitAgree ownerEntries levelEntries projLevelEntry)
open Ix.Cert.StreamRename (StateRen Inert foldl_insOpt_ren)

variable {md md' : Mode}

/-- **A read and its renaming**: renamed declarations, as many generated, renamed blocks
and renamed owners. -/
structure ReadRen (f : md.Id → md'.Id) (rS : Read md) (rA : Read md') : Prop where
  agree : UnitAgree f rS rA
  owners : rA.owners = rS.owners.map (ProjRecOwner.mapKeys f)

/-- What a Source read declares and records lies in the scope: its declarations' names, its
blocks' names and its owners' type formers; and it declares no basis block. -/
structure ReadScoped (P : KeyScope md) (r : Read md) : Prop where
  basis : ∀ d ∈ r.decls.toList, ∀ k, d ≠ .basisDecl k
  names : ∀ d ∈ r.decls.toList, ∀ e ∈ noteEntries d, e.1.Good P
  blocks : ∀ x ∈ r.blocks, x.1.Good P
  owners : ∀ o ∈ r.owners, o.T.Good P

theorem levelEntries_good {P : KeyScope md} {r : Read md} (h : ReadScoped P r) :
    ∀ x ∈ levelEntries r, x.1.Good P := by
  intro x hx
  simp only [levelEntries, List.mem_filterMap] at hx
  obtain ⟨d, hd, he⟩ := hx
  have hd' := List.mem_of_mem_take hd
  cases d with
  | thmDecl cv v =>
    simp only [projLevelEntry] at he
    split at he
    · cases hl : Ix.Kernel.Frontend.projIotaLevel cv.type with
      | none => rw [hl] at he; cases he
      | some l =>
        rw [hl] at he
        cases he
        exact h.names _ hd' (cv.name, cv.levelParams, cv.type, none) (by simp [noteEntries])
    · cases he
  | _ => simp [projLevelEntry] at he

/-- **A read and its renaming keep two related states related**, for a read in the scope. -/
theorem StateRen.commit {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {stS : State md} {stA : State md'} (h : StateRen f P stS stA) {rS : Read md} {rA : Read md'}
    (hr : ReadRen f rS rA) (hs : ReadScoped P rS) :
    StateRen f P (stS.commit rS) (stA.commit rA) := by
  obtain ⟨⟨hdecls, hgen, hblocks⟩, howners⟩ := hr
  have hentries : rA.decls.toList.flatMap noteEntries =
      (rS.decls.toList.flatMap noteEntries).map (renE f) := by
    rw [hdecls, Array.toList_map, List.flatMap_map, List.map_flatMap]
    exact CtxAgree.flatMap_congr' fun d hd => CtxAgree.noteEntries_mapKeys (hs.basis d hd)
  have hkeys : ∀ e ∈ rS.decls.toList.flatMap noteEntries, e.1.Good P := by
    intro e he
    obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
    exact hs.names d hd e he
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [CtxAgree.commit_constTypes, CtxAgree.commit_constTypes, hentries]
    exact foldl_insOpt_ren hf tyOf tyOf (renE f) (fun v => (v.1, v.2.mapKeys f))
      (fun e => rfl) _ (fun e he p hp => by
        unfold tyOf at hp; cases hp; exact hkeys e he)
      _ _ h.types k hk
  · rw [CtxAgree.commit_heights, CtxAgree.commit_heights, hentries]
    have := foldl_insOpt_ren hf htOf htOf (renE f) (fun v : Nat => v)
      (fun e => by rw [CtxAgree.htOf_renE]) _
      (fun e he p hp => by rw [← CtxAgree.htOf_name hp]; exact hkeys e he)
      stS.heights stA.heights (fun k hk => by rw [h.heights k hk, Option.map_id']) k hk
    rw [this, Option.map_id']
  · rw [CtxAgree.commit_indBlocks, CtxAgree.commit_indBlocks, hblocks]
    exact foldl_insOpt_ren hf some some (fun x => (x.1.map f, x.2.mapKeys f)) (BlockRec.mapKeys f)
      (fun x => rfl) _ (fun x hx p hp => by cases hp; exact hs.blocks x hx) _ _ h.blocks k hk
  · rw [CtxAgree.commit_projOwners, CtxAgree.commit_projOwners,
      CtxAgree.ownerEntries_mapKeys howners]
    refine foldl_insOpt_ren hf some some (fun x => (x.1.map f, x.2.mapKeys f))
      (ProjRecOwner.mapKeys f) (fun x => rfl) _ (fun x hx p hp => ?_) _ _ h.owners k hk
    cases hp
    simp only [ownerEntries, List.mem_map] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    exact hs.owners o ho
  · rw [CtxAgree.commit_projLevels, CtxAgree.commit_projLevels,
      CtxAgree.UnitAgree.level_entries ⟨hdecls, hgen, hblocks⟩]
    have := foldl_insOpt_ren hf some some (fun x : CName md × Ix.Kernel.Reader.CLevel => (x.1.map f, x.2))
      (fun l : Ix.Kernel.Reader.CLevel => l)
      (fun x => rfl) _ (fun x hx p hp => by cases hp; exact levelEntries_good hs x hx)
      stS.projLevels stA.projLevels (fun k hk => by rw [h.levels k hk, Option.map_id']) k hk
    rw [this, Option.map_id']

/-! ## Streams of units -/

/-- **The reader's records against quotient Source's reads, unit by unit**, from the Source
state `stS`: a Source read that changes no entry has no record; a record that every related
state reads to nothing has no Source read; any other Source read is in the scope and has one
record, which every reader state related to `stS` reads as the Source read renamed. -/
inductive Units (f : md.Id → md'.Id) (P : KeyScope md) (cx : Ix.Kernel.Reader.Ctx md') :
    State md → List (Read md) → List (Address × Ixon.Constant) → Prop where
  | nil {stS : State md} : Units f P cx stS [] []
  | inertSource {stS : State md} {rS : Read md} {rs : List (Read md)}
      {R : List (Address × Ixon.Constant)} (hr : Inert rS) (tail : Units f P cx (stS.commit rS) rs R) :
      Units f P cx stS (rS :: rs) R
  | inertRecord {stS : State md} {rs : List (Read md)} {a : Address} {c : Ixon.Constant}
      {R : List (Address × Ixon.Constant)}
      (reads : ∀ stA : State md', StateRen f P stS stA →
        ∃ rA, Ix.Kernel.Reader.readRecord cx stA a c = .ok rA ∧ Inert rA)
      (tail : Units f P cx stS rs R) :
      Units f P cx stS rs ((a, c) :: R)
  | record {stS : State md} {rS : Read md} {rs : List (Read md)} {a : Address} {c : Ixon.Constant}
      {R : List (Address × Ixon.Constant)} (hscope : ReadScoped P rS)
      (reads : ∀ stA : State md', StateRen f P stS stA →
        ∃ rA, Ix.Kernel.Reader.readRecord cx stA a c = .ok rA ∧ ReadRen f rS rA)
      (tail : Units f P cx (stS.commit rS) rs R) :
      Units f P cx stS (rS :: rs) ((a, c) :: R)

/-- **The reader reads the units as quotient Source's reads renamed**: from related states,
it reads the records to the Source declarations renamed, and ends related to the Source
state. -/
theorem Units.streamRead {f : md.Id → md'.Id} {P : KeyScope md} (hf : InjOn f P)
    {cx : Ix.Kernel.Reader.Ctx md'} {stS : State md} {rs : List (Read md)}
    {R : List (Address × Ixon.Constant)} (h : Units f P cx stS rs R) :
    ∀ {stA : State md'}, StateRen f P stS stA →
      ∃ stA' out, Ix.Kernel.Reader.StreamRead cx stA R stA' out ∧
        out.toList = (rs.flatMap (·.decls.toList)).map (Declaration.mapKeys f) ∧
        StateRen f P (rs.foldl State.commit stS) stA' := by
  induction h with
  | nil => intro stA hst; exact ⟨stA, #[], .nil, rfl, hst⟩
  | inertSource hr _ ih =>
    intro stA hst
    obtain ⟨stA', out, hread, hout, hfin⟩ := ih (hst.commit_inert_left hr)
    refine ⟨stA', out, hread, ?_, hfin⟩
    rw [hout, List.flatMap_cons, hr.decls]
    rfl
  | inertRecord reads _ ih =>
    intro stA hst
    obtain ⟨rA, hrA, inert⟩ := reads stA hst
    obtain ⟨stA', out, hread, hout, hfin⟩ := ih (hst.commit_inert_right inert)
    refine ⟨stA', rA.decls ++ out, .cons hrA hread, ?_, hfin⟩
    rw [Array.toList_append, hout, inert.decls]
    rfl
  | record hscope reads _ ih =>
    intro stA hst
    obtain ⟨rA, hrA, hren⟩ := reads stA hst
    obtain ⟨stA', out, hread, hout, hfin⟩ := ih (StateRen.commit hf hst hren hscope)
    refine ⟨stA', rA.decls ++ out, .cons hrA hread, ?_, hfin⟩
    rw [Array.toList_append, hout, hren.agree.1, Array.toList_map, List.flatMap_cons, List.map_append]

/-- Plain units are units. -/
theorem Units.of_plain {f : md.Id → md'.Id} {P : KeyScope md} {cx : Ix.Kernel.Reader.Ctx md'}
    {stS : State md} {rs : List (Read md)} {R : List (Address × Ixon.Constant)}
    (h : StreamRename.PlainUnits f P cx stS rs R) : Units f P cx stS rs R := by
  induction h with
  | nil => exact .nil
  | inert hr _ ih => exact .inertSource hr ih
  | record plain hbasis hgood reads _ ih =>
    refine .record ⟨hbasis, hgood, by simp [plain.blocks], by simp [plain.owners]⟩ (fun stA hst => ?_) ih
    obtain ⟨rA, hrA, pA, hdecls⟩ := reads stA hst
    exact ⟨rA, hrA, ⟨⟨hdecls, by rw [pA.generated, plain.generated], by simp [pA.blocks, plain.blocks]⟩,
      by simp [pA.owners, plain.owners]⟩⟩

/-- **A closure read unit by unit concludes as the reader's streams ask**: from the anonymous
prelude state the reader reads the records, keeps the prelude's entries, and its prepared
declarations are quotient Source's prepared declarations renamed. -/
theorem units_conclusion {f : Mode.Id .source → Mode.Id .anon} {Q : Mode.Id .source → Prop}
    (hf : InjOn f Q) {pre : Ix.Kernel.Reader.Prelude .source} {preA : Ix.Kernel.Reader.Prelude .anon}
    (hPA : PreludeAgree.preludeAgreeB pre preA = true) {cx : Ix.Kernel.Reader.Ctx .anon}
    {rs : List (Read .source)} {R : List (Address × Ixon.Constant)}
    (units : Units f (KeyScope.ofId Q) cx pre.state rs R) {decls : Array (CDecl .source)}
    (hdecls : decls.toList = rs.flatMap (·.decls.toList)) (hgood : ∀ d ∈ decls, d.Good Q)
    (hkeep : State.keepsPrelude pre.state (rs.foldl State.commit pre.state) = true) :
    ∃ st' declsA, Ix.Kernel.Reader.StreamRead cx preA.state R st' declsA ∧
      State.keepsPrelude preA.state st' = true ∧
      (Frontend.preparePrelude preA.ix declsA).toList =
        (Frontend.preparePrelude pre.ix decls).toList.map (Declaration.mapKeys f) := by
  have h0 := StateRen.of_prelude (P := KeyScope.ofId Q) (PreludeAgree.preludeAgree_state hPA f)
  obtain ⟨st', out, hread, hout, hfin⟩ := units.streamRead hf h0
  refine ⟨st', out, hread, StreamRename.keepsPrelude_of_agree hPA hfin hkeep, ?_⟩
  have hout' : out = decls.map (Declaration.mapKeys f) :=
    Array.ext' (by rw [hout, Array.toList_map, hdecls])
  rw [hout', PrepareRename.preparePrelude_mapKeys hf (PreludeAgree.preludeAgree_decls hPA f)
    (StreamRename.preludeAgree_declsGood hPA) hgood, Array.toList_map]

/--
info: 'Ix.Cert.StreamUnits.units_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms units_conclusion

end Ix.Cert.StreamUnits
