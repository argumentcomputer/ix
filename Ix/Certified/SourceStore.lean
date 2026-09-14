/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Certified.SourceExpr
import Ix.Theory.Certified.Source

/-! Exact original declaration headers through the source block reader. -/

namespace Ix.Certified

open Ix.Theory Ix.Theory.Certified

theorem mapM_get_right {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    {index : Nat} {value : β} (h : xs.mapM f = some ys) (hy : ys[index]? = some value) :
    ∃ source, xs[index]? = some source ∧ f source = some value := by
  induction xs generalizing ys index with
  | nil => simp at h; subst ys; simp at hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨y, hf, tail, ht, rfl⟩ := h
    cases index with
    | zero => simp at hy; subst value; exact ⟨x, rfl, hf⟩
    | succ index =>
      obtain ⟨source, hs, hf⟩ := ih ht hy
      exact ⟨source, hs, hf⟩

def memberRawHeader : Ixon.MutConst → Nat × Ixon.Expr
  | .defn value => (value.lvls.toNat, value.typ)
  | .recr value => (value.lvls.toNat, value.typ)
  | .indc value => (value.lvls.toNat, value.typ)

def rawHeader? (source : Ixon.Constant) : ConstRef Address → Option (Nat × Ixon.Expr)
  | .member _ index =>
    match source.info with
    | .muts members => members[index]?.map memberRawHeader
    | .defn value => if index = 0 then some (value.lvls.toNat, value.typ) else none
    | .recr value => if index = 0 then some (value.lvls.toNat, value.typ) else none
    | .axio value => if index = 0 then some (value.lvls.toNat, value.typ) else none
    | .quot value => if index = 0 then some (value.lvls.toNat, value.typ) else none
    | _ => none
  | .ctor _ index field => do
    let .muts members := source.info | none
    let .indc family ← members[index]? | none
    let ctor ← family.ctors[field]?
    return (ctor.lvls.toNat, ctor.typ)

def blockHeader? (block : Block Address) : ConstRef Address → Option (Nat × VExpr Address)
  | .member _ index => block.members[index]?.map fun declaration => (declaration.uvars, declaration.type)
  | .ctor _ index field => do
    let .induct _ _ _ _ ctors _ ← block.members[index]? | none
    let ctor ← ctors[field]?
    return (ctor.uvars, ctor.type)

theorem readMember_header {fuel : Nat} {objects : Objects} {naturals : Naturals} {block : Address}
    {source : Ixon.Constant} {member : Ixon.MutConst} {declaration : Const Address}
    (h : readMutualMember? fuel objects naturals block source member = some declaration) :
    declaration.uvars = (memberRawHeader member).1 ∧
      readExpr? fuel objects naturals block source (memberRawHeader member).2 = some declaration.type := by
  cases member with
  | defn value =>
    simp only [readMutualMember?, readDefinition?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨type, ht, body, _, rfl⟩ := h
    exact ⟨rfl, ht⟩
  | recr value =>
    simp only [readMutualMember?, readRecursor?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨type, ht, rules, _, rfl⟩ := h
    exact ⟨rfl, ht⟩
  | indc value =>
    simp only [readMutualMember?, readInductive?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨type, ht, constructors, _, rfl⟩ := h
    exact ⟨rfl, ht⟩

theorem readInductive_constructor {fuel : Nat} {objects : Objects} {naturals : Naturals} {block : Address}
    {source : Ixon.Constant} {family : Ixon.Inductive} {declaration : Const Address}
    {index : Nat} {universes : Nat} {type : VExpr Address}
    (h : readInductive? fuel objects naturals block source family = some declaration)
    (hc : blockHeader? ⟨[declaration]⟩ (.ctor block 0 index) = some (universes, type)) :
    ∃ ctor, family.ctors[index]? = some ctor ∧ ctor.lvls.toNat = universes ∧
      readExpr? fuel objects naturals block source ctor.typ = some type := by
  simp only [readInductive?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨familyType, _, ctors, hm, rfl⟩ := h
  simp only [blockHeader?, List.getElem?_cons_zero, bind, Option.bind_some,
    Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨ctor, hc, hn, ht⟩ := hc
  obtain ⟨⟨raw, position⟩, hr, hp⟩ := mapM_get_right hm hc
  simp only [List.getElem?_zipIdx, Array.getElem?_toList, Nat.zero_add,
    Option.map_eq_some_iff, Prod.mk.injEq] at hr
  obtain ⟨raw', hs, rfl, rfl⟩ := hr
  split at hp
  · contradiction
  · simp only [Option.bind_eq_some_iff, Option.some.injEq] at hp
    obtain ⟨reading, ht', he⟩ := hp
    cases he
    exact ⟨raw', hs, hn, ht ▸ ht'⟩

theorem readBlock_sourceHeader {fuel : Nat} {objects : Objects} {naturals : Naturals} {block : Address}
    {source : Ixon.Constant} {result : Block Address} {ref : ConstRef Address}
    {universes : Nat} {type : VExpr Address}
    (h : readBlock? fuel objects naturals block source = some result)
    (hh : blockHeader? result ref = some (universes, type)) :
    ∃ raw, rawHeader? source ref = some (universes, raw) ∧
      ExprReading objects naturals block source raw type := by
  rcases source with ⟨info, sharing, references, levels⟩
  cases info with
  | defn value =>
    simp only [readBlock?, readDefinition?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, ⟨type, ht, body, _, rfl⟩, rfl⟩ := h
    cases ref with
    | member owner index =>
      cases index with
      | zero =>
        simp only [blockHeader?, List.getElem?_cons_zero, Option.map_some,
          Const.uvars, Const.type, Option.some.injEq, Prod.mk.injEq] at hh
        rcases hh with ⟨rfl, rfl⟩
        exact ⟨_, rfl, readExpr_sound ht⟩
      | succ index => simp [blockHeader?] at hh
    | ctor owner index field => cases index <;> simp [blockHeader?] at hh
  | recr value =>
    simp only [readBlock?, readRecursor?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, ⟨type, ht, rules, _, rfl⟩, rfl⟩ := h
    cases ref with
    | member owner index =>
      cases index with
      | zero =>
        simp only [blockHeader?, List.getElem?_cons_zero, Option.map_some,
          Const.uvars, Const.type, Option.some.injEq, Prod.mk.injEq] at hh
        rcases hh with ⟨rfl, rfl⟩
        exact ⟨_, rfl, readExpr_sound ht⟩
      | succ index => simp [blockHeader?] at hh
    | ctor owner index field => cases index <;> simp [blockHeader?] at hh
  | axio value =>
    simp only [readBlock?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨type, ht, rfl⟩ := h
    cases ref with
    | member owner index =>
      cases index with
      | zero =>
        simp only [blockHeader?, List.getElem?_cons_zero, Option.map_some,
          Const.uvars, Const.type, Option.some.injEq, Prod.mk.injEq] at hh
        rcases hh with ⟨rfl, rfl⟩
        exact ⟨_, rfl, readExpr_sound ht⟩
      | succ index => simp [blockHeader?] at hh
    | ctor owner index field => cases index <;> simp [blockHeader?] at hh
  | quot value =>
    simp only [readBlock?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨type, ht, rfl⟩ := h
    cases ref with
    | member owner index =>
      cases index with
      | zero =>
        simp only [blockHeader?, List.getElem?_cons_zero, Option.map_some,
          Const.uvars, Const.type, Option.some.injEq, Prod.mk.injEq] at hh
        rcases hh with ⟨rfl, rfl⟩
        exact ⟨_, rfl, readExpr_sound ht⟩
      | succ index => simp [blockHeader?] at hh
    | ctor owner index field => cases index <;> simp [blockHeader?] at hh
  | muts rawMembers =>
    simp only [readBlock?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨members, hm, rfl⟩ := h
    cases ref with
    | member owner index =>
      simp only [blockHeader?, Option.map_eq_some_iff, Prod.mk.injEq] at hh
      obtain ⟨declaration, hd, hn, ht⟩ := hh
      obtain ⟨raw, hr, hread⟩ := mapM_get_right hm hd
      have ⟨hu, htype⟩ := readMember_header hread
      refine ⟨(memberRawHeader raw).2, ?_, readExpr_sound (ht ▸ htype)⟩
      simp only [rawHeader?, ← Array.getElem?_toList, hr, Option.map_some]
      exact congrArg some (congrArg (·, (memberRawHeader raw).2) (hu.symm.trans hn))
    | ctor owner index field =>
      simp only [blockHeader?, bind, Option.bind_eq_some_iff] at hh
      obtain ⟨declaration, hd, hc⟩ := hh
      obtain ⟨raw, hr, hread⟩ := mapM_get_right hm hd
      have hc' : blockHeader? ⟨[declaration]⟩ (.ctor block 0 field) = some (universes, type) := by
        simpa only [blockHeader?, List.getElem?_cons_zero, bind, Option.bind_some] using hc
      cases raw with
      | defn value =>
        simp only [readMutualMember?, readDefinition?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hread
        obtain ⟨type, _, body, _, rfl⟩ := hread
        simp [blockHeader?] at hc'
      | recr value =>
        simp only [readMutualMember?, readRecursor?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hread
        obtain ⟨type, _, rules, _, rfl⟩ := hread
        simp [blockHeader?] at hc'
      | indc family =>
        obtain ⟨ctor, hctor, hn, htype⟩ := readInductive_constructor hread hc'
        refine ⟨ctor.typ, ?_, readExpr_sound htype⟩
        have hr' : rawMembers[index]? = some (.indc family) := by simpa using hr
        simp [rawHeader?, hr', hctor, hn]
  | cPrj | rPrj | iPrj | dPrj => simp [readBlock?] at h

theorem lookup_mem {α : Type} {entries : List (Address × α)} {address : Address} {value : α}
    (h : lookup entries address = some value) : (address, value) ∈ entries := by
  induction entries with
  | nil => cases h
  | cons entry rest ih =>
    obtain ⟨key, data⟩ := entry
    unfold lookup at h
    split at h
    · rename_i hk
      subst address
      cases Option.some.inj h
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {α : Type} {entries : List (Address × α)} {address : Address} {value : α}
    (hn : (entries.map Prod.fst).Nodup) (h : (address, value) ∈ entries) :
    lookup entries address = some value := by
  induction entries with
  | nil => cases h
  | cons entry rest ih =>
    obtain ⟨key, data⟩ := entry
    have hn := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with he | hr
    · cases he
      simp [lookup]
    · have hk : address ≠ key := by
        intro he
        apply hn.1
        exact List.mem_map.mpr ⟨(address, value), hr, he⟩
      simp only [lookup, hk, ↓reduceIte]
      exact ih hn.2 hr

theorem readBlocks_mem {fuel : Nat} {objects pending : Objects} {naturals : Naturals}
    {blocks : List (Address × Block Address)} {address : Address} {block : Block Address}
    (h : readBlocks? fuel objects naturals pending = some blocks) (hm : (address, block) ∈ blocks) :
    ∃ source, (address, source) ∈ pending ∧ readBlock? fuel objects naturals address source = some block := by
  induction pending generalizing blocks with
  | nil => simp [readBlocks?] at h; subst blocks; cases hm
  | cons entry rest ih =>
    obtain ⟨key, source⟩ := entry
    unfold readBlocks? at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      obtain ⟨source, hs, hb⟩ := ih h hm
      exact ⟨source, List.mem_cons_of_mem _ hs, hb⟩
    · simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨decoded, hd, tail, ht, rfl⟩ := h
      rcases List.mem_cons.mp hm with he | hr
      · rcases Prod.mk.inj he with ⟨rfl, rfl⟩
        exact ⟨source, List.mem_cons_self .., hd⟩
      · obtain ⟨source, hs, hb⟩ := ih ht hr
        exact ⟨source, List.mem_cons_of_mem _ hs, hb⟩

theorem readStore_sourceBlock {fuel : Nat} {objects : Objects} {naturals : Naturals}
    {store : Store Address} {address : Address} {block : Block Address}
    (h : readStore? fuel objects naturals = some store) (hb : store.blocks address = some block) :
    ∃ source, lookup objects address = some source ∧ readBlock? fuel objects naturals address source = some block := by
  unfold readStore? at h
  split at h
  · rename_i hn
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨blocks, hblocks, h⟩ := h
    split at h
    · cases Option.some.inj h
      obtain ⟨source, hs, hr⟩ := readBlocks_mem hblocks (lookup_mem hb)
      exact ⟨source, lookup_of_mem hn hs, hr⟩
    · cases h
  · cases h

def storeHeader? (store : Store Address) (ref : ConstRef Address) : Option (Nat × VExpr Address) := do
  let block ← store.blocks ref.block
  blockHeader? block ref

theorem storeHeader_maps (store : Store Address) (ref : ConstRef Address) :
    (storeHeader? store ref).map Prod.fst = store.uvars ref ∧
    (storeHeader? store ref).map Prod.snd = store.type ref := by
  cases ref with
  | member address index =>
    cases hs : store.blocks address with
    | none => simp [storeHeader?, ConstRef.block, Store.type, Store.uvars, Store.lookup, Store.lookupCtor, hs]
    | some block =>
      cases hm : block.members[index]? <;>
        simp [storeHeader?, ConstRef.block, blockHeader?, Store.type, Store.uvars, Store.lookup, Store.lookupCtor, hs, hm]
  | ctor address index field =>
    cases hs : store.blocks address with
    | none => simp [storeHeader?, ConstRef.block, Store.type, Store.uvars, Store.lookup, Store.lookupCtor, hs]
    | some block =>
      cases hm : block.members[index]? with
      | none => simp [storeHeader?, ConstRef.block, blockHeader?, Store.type, Store.uvars, Store.lookup, Store.lookupCtor, hs, hm]
      | some declaration =>
        cases declaration <;>
          simp [storeHeader?, ConstRef.block, blockHeader?, Store.type, Store.uvars, Store.lookup, Store.lookupCtor, hs, hm]
        rename_i ctors _
        cases hc : ctors[field]? <;> simp

theorem sourceHeader_pair {store : Store Address} {ref : ConstRef Address} {entry : Ix.Theory.Model.ConstantEntry Address}
    (h : SourceHeader store ref entry) : storeHeader? store ref = some (entry.universes, entry.type.erase) := by
  have ⟨hu, ht⟩ := storeHeader_maps store ref
  rw [h.universes] at hu
  rw [h.type] at ht
  cases hh : storeHeader? store ref with
  | none => simp [hh] at ht
  | some header =>
    rcases header with ⟨universes, type⟩
    simp only [hh, Option.map_some, Option.some.injEq] at hu ht
    cases hu
    cases ht
    rfl

/-- Exact source type, source universe arity and a unique structural reading
of that original type, for every admitted source member or constructor. -/
theorem readStore_sourceHeader {fuel : Nat} {objects : Objects} {naturals : Naturals}
    {store : Store Address} {ref : ConstRef Address} {entry : Ix.Theory.Model.ConstantEntry Address}
    (h : readStore? fuel objects naturals = some store) (hh : SourceHeader store ref entry) :
    ∃ source raw, lookup objects ref.block = some source ∧
      rawHeader? source ref = some (entry.universes, raw) ∧
      ExprReading objects naturals ref.block source raw entry.type.erase := by
  have hp := sourceHeader_pair hh
  simp only [storeHeader?, bind, Option.bind_eq_some_iff] at hp
  obtain ⟨block, hb, hp⟩ := hp
  obtain ⟨source, hs, hr⟩ := readStore_sourceBlock h hb
  obtain ⟨raw, hraw, hread⟩ := readBlock_sourceHeader hr hp
  exact ⟨source, raw, hs, hraw, hread⟩

end Ix.Certified
