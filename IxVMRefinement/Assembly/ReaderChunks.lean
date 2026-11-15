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
    · have htail : ∀ d' ∈ ds, InstallChunk d' (declarationChunk env d') :=
        fun d' hd' => declarationChunk_spec (hcoverage d' (List.mem_cons_of_mem d hd'))
      induction ds with
      | nil => exact .nil
      | cons d' ds ih =>
        exact .cons (htail d' List.mem_cons_self)
          (ih (fun d'' hd'' => hcoverage d'' (by simp [hd'']))
            (fun d'' hd'' => htail d'' (List.mem_cons_of_mem d' hd'')))

/-- The final checked constants determine an actual reader-order installation. All projection
tables are assigned to the first step as allowed auxiliary constants. -/
theorem installs_readerChunks {env : Env .anon} {ds : List (Declaration .anon)}
    (henv : (env.consts.map (·.name)).Nodup) (hds : (publicReaderKeys ds).Nodup)
    (hnonaux : ∀ k ∈ publicReaderKeys ds, ∀ base auxTag, k ≠ .aux base auxTag)
    (hcoverage : ∀ d ∈ ds, ∀ ci₀ ∈ IxVM.Consistency.installs d,
      ∃ ci ∈ env.consts, IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.Installs ds ⟨(readerChunks env ds).reverse.flatten⟩ :=
  installs_of_chunks (readerChunks_spec hcoverage) (readerChunks_nodup henv hds hnonaux)

end IxVM.Refinement.Assembly
