module

public import IxC.Kernel.Rules.TransportKit
public import IxC.Kernel.Verify.EnvWF

public section

/-!
# A well-formed environment stores closed terms

`StoreClosed` (`Rules/TransportKit.lean`) is what the renaming half of the rules'
transport (`Rules/Transport.lean`, top weakening) asks of the environment: the stored types,
definition values, recursor right-hand sides and nested pins, and projection-table
bodies have no free variables. `EnvWF` records exactly these, so every
environment the kernel's install invariant covers satisfies it.
-/

namespace Ix.Kernel

private theorem find?_mem' {env : Env md} {n : Key md} {ci : ConstantInfo md}
    (h : env.find? n = some ci) : ci ∈ env.consts := by
  unfold Env.find? at h
  exact List.mem_of_find?_eq_some h

/-- **A well-formed environment stores closed terms.** -/
theorem StoreClosed.of_envWF {env : Env md} (h : EnvWF env) : StoreClosed env where
  type := fun hf => (h _ (find?_mem' hf)).1
  defn := fun hf => ((h _ (find?_mem' hf)).2.2.2.2.1 _ _ _ rfl).1
  rhs := fun hf rl hrl => by
    have hr := (h _ (find?_mem' hf)).2.2.2.2.2.1 _ _ _ _ rfl rl hrl
    exact ⟨hr.1, fun lvls pins hfire p hp => ((hr.2.2.2.2 lvls pins hfire).2.2.1 p hp).1⟩
  proj := fun {_ i _} hent => by
    obtain ⟨tbl, hf, hi, rfl⟩ := Env.findProj?_some hent
    obtain ⟨hsz, hb⟩ := (h _ (find?_mem' hf)).2.2.2.2.2.2.1 tbl rfl
    have hi' : i < tbl.bodies.size := hsz ▸ hi
    have hget : tbl.bodies[i]? = some tbl.bodies[i] := by simp [hi']
    have hbody : (tbl.entry i).body = tbl.bodies[i] := by
      simp [ProjTable.entry, hi']
    rw [hbody]
    exact (hb i _ hget).1

end Ix.Kernel
