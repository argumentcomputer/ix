import Ix.Cert.SourceOrigin

/-! # Generated bases in an actual inductive read

The generator's base-origin theorem applies to the block that lowerInductive
actually builds. Its type list is a zip, so the origin-to-closing-name bridge
uses inclusion and requires no length or well-formedness premise. The public
endpoints address generated entries, including ordinary-key and renamed-block
forms for CtxAgree.Streams.baseS/baseA. Pairing, no-drop and acceptance remain
separate obligations.
-/

namespace Ix.Cert.SourceOriginRead

open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Frontend.InModel Ix.Cert.CtxAgree

variable {md md' : Mode}

theorem blockNames_eq (rb : BlockRead md) :
    blockNames rb = rb.types.toList.map (fun x => x.1.name) ++
      rb.ctors.toList.map (fun x => x.1.name) ++ rb.recs.toList.map (fun x => x.1.name) := by
  simp only [blockNames, noteEntries, indDeclOf, List.map_append, List.map_map]
  rfl

/-- The modeller's truncated type zip can remove names, but adds none. -/
theorem roots_blockRecOf {rb : BlockRead md} {k : Key md}
    (h : k ∈ SourceOrigin.roots (blockRecOf rb)) : k ∈ (blockNames rb).map Key.base := by
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
  apply List.mem_map.mpr
  refine ⟨n, ?_, rfl⟩
  rw [blockNames_eq]
  simp only [blockRecOf, List.map_map, List.mem_append] at hn
  rcases hn with (ht | hc) | hr
  · obtain ⟨⟨t, cs⟩, hzip, rfl⟩ := List.mem_map.mp ht
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.mpr ⟨t, (List.of_mem_zip hzip).1, rfl⟩))
  · exact List.mem_append_left _ (List.mem_append_right _ hc)
  · exact List.mem_append_right _ hr

/-- A noted entry names a declaration key when the declaration is nonempty.
The internal basis record has no declared names and is excluded explicitly. -/
theorem entry_name {d : Declaration md} (hne : d.names ≠ []) {e : Entry md}
    (he : e ∈ noteEntries d) : e.1 ∈ d.names := by
  have eq : (noteEntries d).map Prod.fst = d.names := by
    cases d with
    | basisDecl => exact (hne rfl).elim
    | indDecl block n => simp only [noteEntries, Declaration.names, List.map_map]; rfl
    | _ => rfl
  rw [← eq]
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-- Base origin for the generated prefix of the actual successful read. -/
theorem lowerInductive_bases {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r) :
    ∀ e ∈ genEntries r, e.1.base ∈ (blockNames rb).map Key.base := by
  obtain ⟨gens, hd, hg, _, hc⟩ := lowerInductive_ok h
  intro e he
  simp only [genEntries, hd, hg, Array.toList_push, List.take_left] at he
  obtain ⟨d, hd, he⟩ := List.mem_flatMap.mp he
  rcases hc with ⟨_, hgen⟩ | ⟨_, rfl⟩
  · exact roots_blockRecOf (SourceOrigin.generate_bases hgen d hd e.1
      (entry_name (SourceNames.generate_names hgen hd).1 he))
  · cases hd

theorem base_of_not_aux {k : Key md} (h : k.isAux = false) : k.base = k := by
  cases k <;> first | rfl | cases h

/-- Ordinary closing keys give exactly the baseS shape, with no extra
generation or distinctness assumption. -/
theorem lowerInductive_bases_ordinary {st : State md} {rb : BlockRead md} {r : Read md}
    (h : lowerInductive st rb = .ok r)
    (ordinary : ∀ k ∈ blockNames rb, k.isAux = false) :
    ∀ e ∈ genEntries r, e.1.base ∈ blockNames rb := by
  intro e he
  obtain ⟨k, hk, eq⟩ := List.mem_map.mp (lowerInductive_bases h e he)
  rw [base_of_not_aux (ordinary k hk)] at eq
  exact eq ▸ hk

theorem blockNames_mapKeys (f : md.Id → md'.Id) (rb : BlockRead md) :
    blockNames (rb.mapKeys f) = (blockNames rb).map (Key.map f) := by
  simp only [blockNames_eq, BlockRead.mapKeys, Array.toList_map,
    List.map_append, List.map_map]
  rfl

/-- The corresponding baseA shape for a read of the renamed block. This
does not assert that any Source unit has that target read as its partner. -/
theorem lowerInductive_bases_mapKeys (f : md.Id → md'.Id)
    {st : State md'} {rb : BlockRead md} {r : Read md'}
    (h : lowerInductive st (rb.mapKeys f) = .ok r)
    (ordinary : ∀ k ∈ blockNames rb, k.isAux = false) :
    ∀ e ∈ genEntries r, e.1.base ∈ (blockNames rb).map (Key.map f) := by
  rw [← blockNames_mapKeys]
  apply lowerInductive_bases_ordinary h
  intro k hk
  rw [blockNames_mapKeys] at hk
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hk
  rw [CtxAgree.Key.map_isAux]
  exact ordinary n hn

open Ix.LeanIngress in
/-- Actual quotient conversion supplies the ordinary-key premise internally.
The read is still raw: collapse/no-drop and stream pairing are not inferred. -/
theorem quotient_lowerInductive_bases {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
    {gr : Group} {c : Converted} (converted : convert gr = .ok c)
    (hints : CName .source → Option ReducibilityHint) {rb : BlockRead .source}
    (quotient : (c.withHints hints).quotient (fiberAliasAt ixe roles) = .inductive rb)
    {st : State .source} {r : Read .source} (lowered : lowerInductive st rb = .ok r) :
    ∀ e ∈ genEntries r, e.1.base ∈ blockNames rb := by
  apply lowerInductive_bases_ordinary lowered
  have ordinary := SourceNames.quotient_lower_ordinary converted hints
    (st := st) (r := r) (by rw [quotient]; exact lowered)
  obtain ⟨gens, hd, hg, _, _⟩ := lowerInductive_ok lowered
  have names : (indDeclOf rb).names = blockNames rb := by
    simp only [blockNames, noteEntries, indDeclOf, Declaration.names, List.map_map]
    rfl
  intro k hk
  apply ordinary (indDeclOf rb) (by simp [hd, hg]) k
  rwa [names]

end Ix.Cert.SourceOriginRead
