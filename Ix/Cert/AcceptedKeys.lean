import Ix.Cert.Composition

/-! # The keys of an accepted environment are unique

The pure fold pushes a constant only under a name its environment misses
(`checkConstantVal`'s duplicate check, `installBasisDecl`'s, the inductive
routes' member and table checks), and no declaration pushes two constants
under one name. `Ix.Kernel.foldlM_checkDecl_post` records both as growth from
the empty environment (`Ix.Kernel.Grows`), so a reference accept's names are
pairwise distinct (`nodup`), and every installed constant is what a lookup of
its own name returns (`find_mem`).

At quotient Source's environment this is the first half of the Source
totality obligation (`sourceKeys_unique`). -/

namespace Ix.Cert.AcceptedKeys

/-- In a list whose names are pairwise distinct, a lookup of a member's name
finds that member. -/
theorem find?_name_of_nodup {md : Ix.Kernel.Mode} :
    ∀ {l : List (Ix.Kernel.ConstantInfo md)}, (l.map (·.name)).Nodup →
      ∀ c ∈ l, l.find? (·.name == c.name) = some c
  | [], _, _, h => nomatch h
  | c' :: l, hnd, c, hc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hc with rfl | hc
    · simp
    · have hne : (c'.name == c.name) = false := by
        refine beq_eq_false_iff_ne.mpr fun he => hnd.1 ?_
        rw [he]
        exact List.mem_map_of_mem hc
      rw [List.find?_cons, hne]
      exact find?_name_of_nodup hnd.2 c hc

/-- **A reference accept's names are pairwise distinct.** -/
theorem nodup {md : Ix.Kernel.Mode} {μ : Ix.Kernel.CheckMode} {ev : Ix.Kernel.Evidences md}
    {ds : List (Ix.Kernel.Declaration md)} {env : Ix.Kernel.Env md}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds env) : (env.consts.map (·.name)).Nodup := by
  obtain ⟨F, h⟩ := h
  exact (Ix.Kernel.foldlM_checkDecl_post μ (Ix.Kernel.fueledOps μ F) ev ds Ix.Kernel.Env.empty env
    h).nodup List.nodup_nil

/-- **A reference accept installs each key once**: a lookup of an installed
constant's name returns that constant. -/
theorem find_mem {md : Ix.Kernel.Mode} {μ : Ix.Kernel.CheckMode} {ev : Ix.Kernel.Evidences md}
    {ds : List (Ix.Kernel.Declaration md)} {env : Ix.Kernel.Env md}
    (h : Ix.Kernel.Cached.AcceptsRef μ ev ds env) :
    ∀ c ∈ env.consts, env.find? c.name = some c :=
  find?_name_of_nodup (nodup h)

/-- **Quotient Source installs each key once.** -/
theorem sourceKeys_unique {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} {t : Ix.Kernel.RoleTable} {envQ : Ix.Kernel.Env .source}
    (h : Premises env roots sub ixe failures t envQ) :
    ∀ c ∈ envQ.consts, envQ.find? c.name = some c := by
  obtain ⟨-, _, _, -, -, accepted⟩ := h.source
  exact find_mem accepted

/-- info: 'Ix.Cert.AcceptedKeys.find_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms find_mem

/-- info: 'Ix.Cert.AcceptedKeys.sourceKeys_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sourceKeys_unique

end Ix.Cert.AcceptedKeys
