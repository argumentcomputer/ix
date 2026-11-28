import IxCC.X86.Layout.Proof.Linearize

/-!
# Layout as one simulation

`Backend.lay` tunnels the stacked program and then runs `Layout.run`
(`Order.check` and `linearize`) on the tunnelled one; `Backend.finish`
checks the result (`Program.checkK`, equal to `Program.check`). `transport`
composes the two simulations: a `Stream.SafeSteps` run of the stacked
program from its initial machine with an empty mask becomes a run of the
laid-out program from its initial machine, with the same final mask, at
most as many steps and at least `1/(blocks + 1)` as many (tunnelling skips
empty jumps), ending in a machine with the same status and, given that the
caller's return-address bytes are not masked, the same `Exit`. -/

namespace IxCC.X86.Layout.Proof

open IxCC.X86
open IxCC.X86.Stream

/-- Layout (tunnelling, the checked order, linearisation) transports a safe
typed run of the stacked program to the laid-out program. -/
theorem transport {runtime : Runtime} {cs cq : Checked} {s : Shape} {o : Order} {q : Program}
    {pos : NatMap Nat} (h : Layout.run (tunnel cs.program) s o = .ok (q, pos)) (hq : cq.program = q)
    {n : Nat} {holes holes' : Holes} {core₀ : Core} {m₁ : Machine}
    (steps : SafeSteps runtime cs n holes (Machine.initial cs core₀) holes' m₁) :
    ∃ n' mt m₁', SafeSteps runtime cq n' holes (Machine.initial cq core₀) holes' m₁' ∧
      n' ≤ n ∧ n ≤ (cs.program.blocks.size + 1) * n' ∧
      (∃ k, TRel cs.program k m₁ mt) ∧ LRel (tunnel cs.program) o.flatten holes' mt m₁' := by
  obtain ⟨nt, k, mt, stepsT, relT, hle, hbound⟩ := tunnel_run (c' := tunnelChecked cs) rfl steps
  obtain ⟨m₁', stepsQ, relL⟩ := linearize_run (cp := tunnelChecked cs) rfl hq h stepsT
  exact ⟨nt, mt, m₁', stepsQ, hle, hbound, ⟨k, relT⟩, relL⟩

/-- The end of a transported run: a running machine stays running, a
result stays the same, and an `Exit` transfers when the caller's
return-address bytes are not masked. -/
theorem transport_end {p : Program} {order : List Nat} {cs : Checked} {k : Nat} {holes : Holes}
    {m₁ mt m₁' : Machine} (relT : TRel cs.program k m₁ mt) (relL : LRel p order holes mt m₁') :
    (m₁.status = .running → m₁'.status = .running) ∧
      (∀ v, m₁.status = .halted v → m₁'.status = .halted v) ∧
      (∀ {core₀ : Core} {retAddr st val : Word}, Exit core₀ retAddr st val m₁ →
        ReadableData holes (m₁.core.readReg .rsp) 8 → Exit core₀ retAddr st val m₁') ∧
      m₁'.core.registers = m₁.core.registers := by
  refine ⟨fun running => relL.running (relT.running running), fun v halted => relL.halted (by rw [relT.status, halted]),
    fun exit data => relL.exit (relT.exit exit) (by rw [relT.core]; exact data), ?_⟩
  rw [relL.registers, relT.core]

end IxCC.X86.Layout.Proof
