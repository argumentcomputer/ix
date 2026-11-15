import IxVMRefinement.Assembly.InstallChunks
import IxVMRefinement.Assembly.SelectedEnv

/-! # Concrete chunks of the final checked store for reader-order installation -/

namespace IxVM.Refinement.Assembly

open Ix.Kernel

def declarationKeys (d : Declaration .anon) : List (Key .anon) :=
  (IxVM.Consistency.installs d).map (·.name)

def publicReaderKeys (ds : List (Declaration .anon)) : List (Key .anon) :=
  ds.flatMap declarationKeys

def declarationChunk (env : Env .anon) (d : Declaration .anon) : List (ConstantInfo .anon) :=
  env.consts.filter fun ci => (declarationKeys d).contains ci.name

def tableChunk (env : Env .anon) : List (ConstantInfo .anon) :=
  env.consts.filter fun | .projInfo _ => true | _ => false

def readerChunks (env : Env .anon) : List (Declaration .anon) → List (List (ConstantInfo .anon))
  | [] => []
  | d :: ds => (tableChunk env ++ declarationChunk env d) :: ds.map (declarationChunk env)

theorem mem_declarationChunk {env : Env .anon} {d : Declaration .anon}
    {ci : ConstantInfo .anon} :
    ci ∈ declarationChunk env d ↔ ci ∈ env.consts ∧ ci.name ∈ declarationKeys d := by
  simp only [declarationChunk, List.mem_filter, List.contains_iff_mem]

theorem declarationChunk_spec {env : Env .anon} {d : Declaration .anon}
    (hcoverage : ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ ci ∈ env.consts, IxVM.Consistency.StoredAs ci ci₀) :
    InstallChunk d (declarationChunk env d) := by
  constructor
  · intro ci₀ hci₀
    obtain ⟨ci, hci, hstored⟩ := hcoverage ci₀ hci₀
    refine ⟨ci, mem_declarationChunk.mpr ⟨hci, ?_⟩, hstored⟩
    rw [hstored.name_eq]
    exact List.mem_map.mpr ⟨ci₀, hci₀, rfl⟩
  · intro ci hci
    obtain ⟨ci₀, hci₀, hname⟩ := List.mem_map.mp (mem_declarationChunk.mp hci).2
    exact .inl ⟨ci₀, hci₀, hname⟩

theorem declarationChunk_nodup {env : Env .anon} {d : Declaration .anon}
    (hnd : (env.consts.map (·.name)).Nodup) :
    ((declarationChunk env d).map (·.name)).Nodup := by
  have hsub : (declarationChunk env d).Sublist env.consts := List.filter_sublist
  exact (hsub.map (·.name)).nodup hnd

theorem plainChunks_key {env : Env .anon} {ds : List (Declaration .anon)}
    {ci : ConstantInfo .anon} (hci : ci ∈ (ds.map (declarationChunk env)).flatten) :
    ci.name ∈ publicReaderKeys ds := by
  obtain ⟨chunk, hchunk, hm⟩ := List.mem_flatten.mp hci
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hchunk
  exact List.mem_flatMap.mpr ⟨d, hd, (mem_declarationChunk.mp hm).2⟩

theorem plainChunks_nodup (env : Env .anon)
    (henv : (env.consts.map (·.name)).Nodup) :
    ∀ (ds : List (Declaration .anon)), (publicReaderKeys ds).Nodup →
      ((ds.map (declarationChunk env)).flatten.map (·.name)).Nodup
  | [], _ => by simp
  | d :: ds, hds => by
    simp only [publicReaderKeys, List.flatMap_cons, List.nodup_append] at hds
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.nodup_append]
    refine ⟨declarationChunk_nodup henv, plainChunks_nodup env henv ds hds.2.1, ?_⟩
    intro x hx y hy hxy
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hx
    obtain ⟨cj, hcj, rfl⟩ := List.mem_map.mp hy
    exact hds.2.2 ci.name (mem_declarationChunk.mp hci).2 cj.name (plainChunks_key hcj) hxy

theorem mem_tableChunk {env : Env .anon} {ci : ConstantInfo .anon} :
    ci ∈ tableChunk env ↔ ci ∈ env.consts ∧ ∃ tbl, ci = .projInfo tbl := by
  cases ci <;> simp [tableChunk]

theorem tableChunk_aux {env : Env .anon} {ci : ConstantInfo .anon}
    (hci : ci ∈ tableChunk env) : ∃ k auxTag, ci.name = .aux k auxTag := by
  obtain ⟨_, tbl, rfl⟩ := mem_tableChunk.mp hci
  exact ⟨tbl.structName, .projTable, rfl⟩

theorem tableChunk_nodup {env : Env .anon} (hnd : (env.consts.map (·.name)).Nodup) :
    ((tableChunk env).map (·.name)).Nodup := by
  have hsub : (tableChunk env).Sublist env.consts := List.filter_sublist
  exact (hsub.map (·.name)).nodup hnd

theorem readerChunks_flatten {env : Env .anon} {ds : List (Declaration .anon)}
    (hne : ds ≠ []) :
    (readerChunks env ds).flatten = tableChunk env ++ (ds.map (declarationChunk env)).flatten := by
  cases ds with
  | nil => exact (hne rfl).elim
  | cons d ds => simp [readerChunks, List.append_assoc]

theorem readerChunks_nodup {env : Env .anon} {ds : List (Declaration .anon)}
    (henv : (env.consts.map (·.name)).Nodup) (hds : (publicReaderKeys ds).Nodup)
    (hnonaux : ∀ k ∈ publicReaderKeys ds, ∀ base auxTag, k ≠ .aux base auxTag) :
    ((readerChunks env ds).flatten.map (·.name)).Nodup := by
  cases ds with
  | nil => simp [readerChunks]
  | cons d ds =>
    rw [readerChunks_flatten (by simp), List.map_append, List.nodup_append]
    refine ⟨tableChunk_nodup henv, plainChunks_nodup env henv _ hds, ?_⟩
    intro x hx y hy hxy
    obtain ⟨ci, hci, rfl⟩ := List.mem_map.mp hx
    obtain ⟨cj, hcj, rfl⟩ := List.mem_map.mp hy
    obtain ⟨base, auxTag, haux⟩ := tableChunk_aux hci
    exact hnonaux cj.name (plainChunks_key hcj) base auxTag (hxy.symm.trans haux)

private theorem plainChunks_spec (env : Env .anon) :
    ∀ (ds : List (Declaration .anon)),
      (∀ d ∈ ds, ∀ ci₀ ∈ IxVM.Consistency.installs d,
        ∃ ci ∈ env.consts, IxVM.Consistency.StoredAs ci ci₀) →
      List.Forall₂ InstallChunk ds (ds.map (declarationChunk env))
  | [], _ => .nil
  | d :: ds, hcoverage =>
    .cons (declarationChunk_spec (hcoverage d List.mem_cons_self))
      (plainChunks_spec env ds (fun d' hd' => hcoverage d' (List.mem_cons_of_mem d hd')))

theorem readerChunks_spec {env : Env .anon} {ds : List (Declaration .anon)}
    (hcoverage : ∀ d ∈ ds, ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ ci ∈ env.consts, IxVM.Consistency.StoredAs ci ci₀) :
    List.Forall₂ InstallChunk ds (readerChunks env ds) := by
  cases ds with
  | nil => exact .nil
  | cons d ds =>
    have hd := declarationChunk_spec (hcoverage d List.mem_cons_self)
    refine .cons ⟨?_, ?_⟩ ?_
    · intro ci₀ hci₀
      obtain ⟨ci, hci, hstored⟩ := hd.1 ci₀ hci₀
      exact ⟨ci, List.mem_append_right _ hci, hstored⟩
    · intro ci hci
      rcases List.mem_append.mp hci with htable | hdecl
      · exact .inr (tableChunk_aux htable)
      · exact hd.2 ci hdecl
    · exact plainChunks_spec env ds (fun d' hd' => hcoverage d' (List.mem_cons_of_mem d hd'))

/-- The final checked constants determine an actual reader-order installation. All projection
tables are assigned to the first step as allowed auxiliary constants. -/
theorem installs_readerChunks {env : Env .anon} {ds : List (Declaration .anon)}
    (henv : (env.consts.map (·.name)).Nodup) (hds : (publicReaderKeys ds).Nodup)
    (hnonaux : ∀ k ∈ publicReaderKeys ds, ∀ base auxTag, k ≠ .aux base auxTag)
    (hcoverage : ∀ d ∈ ds, ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ ci ∈ env.consts, IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.Installs ds ⟨(readerChunks env ds).reverse.flatten⟩ :=
  installs_of_chunks (readerChunks_spec hcoverage) (readerChunks_nodup henv hds hnonaux)

def readerSelectionKey (env : Env .anon) (ds : List (Declaration .anon)) (k : Key .anon) : Prop :=
  k ∈ publicReaderKeys ds ∨ ∃ tbl, env.find? k = some (.projInfo tbl)

def readerChunkEnv (env : Env .anon) (ds : List (Declaration .anon)) : Env .anon :=
  ⟨(readerChunks env ds).reverse.flatten⟩

theorem mem_plainChunks {env : Env .anon} {ds : List (Declaration .anon)}
    {ci : ConstantInfo .anon} :
    ci ∈ (ds.map (declarationChunk env)).flatten ↔
      ci ∈ env.consts ∧ ci.name ∈ publicReaderKeys ds := by
  constructor
  · intro hm
    obtain ⟨chunk, hchunk, hci⟩ := List.mem_flatten.mp hm
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hchunk
    exact ⟨(mem_declarationChunk.mp hci).1,
      List.mem_flatMap.mpr ⟨d, hd, (mem_declarationChunk.mp hci).2⟩⟩
  · rintro ⟨hci, hname⟩
    obtain ⟨d, hd, hkey⟩ := List.mem_flatMap.mp hname
    exact List.mem_flatten.mpr ⟨declarationChunk env d, List.mem_map.mpr ⟨d, hd, rfl⟩,
      mem_declarationChunk.mpr ⟨hci, hkey⟩⟩

theorem mem_readerChunkEnv {env : Env .anon} {ds : List (Declaration .anon)}
    (hne : ds ≠ []) {ci : ConstantInfo .anon} :
    ci ∈ (readerChunkEnv env ds).consts ↔
      ci ∈ env.consts ∧ ((∃ tbl, ci = .projInfo tbl) ∨ ci.name ∈ publicReaderKeys ds) := by
  have hreverse : ci ∈ (readerChunks env ds).reverse.flatten ↔
      ci ∈ (readerChunks env ds).flatten := by
    simp only [List.mem_flatten, List.mem_reverse]
  change ci ∈ (readerChunks env ds).reverse.flatten ↔ _
  rw [hreverse, readerChunks_flatten hne, List.mem_append, mem_tableChunk, mem_plainChunks]
  constructor
  · rintro (⟨hm, hp⟩ | ⟨hm, hn⟩)
    · exact ⟨hm, .inl hp⟩
    · exact ⟨hm, .inr hn⟩
  · rintro ⟨hm, hp | hn⟩
    · exact .inl ⟨hm, hp⟩
    · exact .inr ⟨hm, hn⟩

private theorem reader_find_of_mem {env : Env .anon}
    (hnd : (env.consts.map (·.name)).Nodup) {ci : ConstantInfo .anon}
    (hci : ci ∈ env.consts) : env.find? ci.name = some ci := by
  cases hf : env.find? ci.name with
  | none => exact (List.find?_eq_none.mp hf ci hci (beq_self_eq_true _)).elim
  | some ci' =>
    have heq := IxVM.Consistency.eq_of_name_eq hnd
      (Semantics.Env.find?_mem hf) hci (Semantics.Env.find?_name hf)
    exact congrArg some heq

theorem readerSelectionKey_of_mem {env : Env .anon} {ds : List (Declaration .anon)}
    (hnd : (env.consts.map (·.name)).Nodup) {ci : ConstantInfo .anon}
    (hci : ci ∈ env.consts) :
    readerSelectionKey env ds ci.name ↔
      ci.name ∈ publicReaderKeys ds ∨ ∃ tbl, ci = .projInfo tbl := by
  constructor
  · rintro (hname | ⟨tbl, hf⟩)
    · exact .inl hname
    · exact .inr ⟨tbl, IxVM.Consistency.eq_of_name_eq hnd hci
        (Semantics.Env.find?_mem hf) (Semantics.Env.find?_name hf).symm⟩
  · rintro (hname | ⟨tbl, rfl⟩)
    · exact .inl hname
    · exact .inr ⟨tbl, reader_find_of_mem hnd hci⟩

theorem readerChunkEnv_members_select {env : Env .anon} {ds : List (Declaration .anon)}
    (hnd : (env.consts.map (·.name)).Nodup) (hne : ds ≠ []) (ci : ConstantInfo .anon) :
    ci ∈ (readerChunkEnv env ds).consts ↔
      ci ∈ (selectEnv env (readerSelectionKey env ds)).consts := by
  rw [mem_readerChunkEnv hne, mem_selectEnv]
  constructor
  · rintro ⟨hm, hp | hn⟩
    · exact ⟨hm, (readerSelectionKey_of_mem hnd hm).mpr (.inr hp)⟩
    · exact ⟨hm, .inl hn⟩
  · rintro ⟨hm, hk⟩
    rcases (readerSelectionKey_of_mem hnd hm).mp hk with hn | hp
    · exact ⟨hm, .inr hn⟩
    · exact ⟨hm, .inl hp⟩

/-- The actual final stored annotations inherit support from the reader declarations.
Projection tables have closed sort types and require no additional constant support here. -/
theorem readerSelection_supported {env : Env .anon} {ds : List (Declaration .anon)}
    (hnd : (env.consts.map (·.name)).Nodup)
    (hcoverage : ∀ d ∈ ds, ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ ci ∈ env.consts, IxVM.Consistency.StoredAs ci ci₀)
    (hreader : ∀ d ∈ ds, ∀ ci₀ ∈ IxVM.Consistency.installs d,
      SupportedConstant (readerSelectionKey env ds) ci₀) :
    ∀ ci ∈ env.consts, readerSelectionKey env ds ci.name →
      SupportedConstant (readerSelectionKey env ds) ci := by
  intro ci hci hkey
  rcases hkey with hname | ⟨tbl, hf⟩
  · obtain ⟨d, hd, hname⟩ := List.mem_flatMap.mp hname
    obtain ⟨ci₀, hci₀, hname⟩ := List.mem_map.mp hname
    obtain ⟨stored, hstored_mem, hstored⟩ := hcoverage d hd ci₀ hci₀
    have heq : ci = stored := IxVM.Consistency.eq_of_name_eq hnd hci hstored_mem
      (hname.symm.trans hstored.name_eq.symm)
    rw [heq]
    exact storedAs_supports hstored (hreader d hd ci₀ hci₀)
  · have heq : ci = .projInfo tbl := IxVM.Consistency.eq_of_name_eq hnd hci
      (Semantics.Env.find?_mem hf) (Semantics.Env.find?_name hf).symm
    subst ci
    exact ⟨.inr ⟨tbl, hf⟩, trivial, trivial⟩

end IxVM.Refinement.Assembly
