import IxCC.X86.Layout.Proof.Transport

/-!
# Layout from any root

`transport` carries a run of the stacked program from its entry to the
laid-out program from its entry. The layout shape's roots (every export's
wrapper) are reachable, so `Order.check` places them, and linearisation
renumbers them like any placed block. `transport_at` carries a run of the
stacked program started at a root `b` to the laid-out program started at
`b`'s new number (`renum`): the same tunnelling and linearisation
simulations, from the two programs started elsewhere.

- `reach_mono`, `reach_frontier`, `reachable_root`: the reachability walk
  keeps what it has seen and sees its first frontier, so every root is
  reachable;
- `root_placed`: an accepted order places every root.
-/

namespace IxCC.X86.Layout.Proof

open IxCC.X86
open IxCC.X86.Stream

/-- The walk keeps what it has seen. -/
theorem reach_mono (m : NatMap Block) :
    ∀ (fuel : Nat) (seen : NatSet) (frontier : List Nat) (b : Nat), seen.contains b = true →
      (reach m fuel seen frontier).contains b = true
  | 0, _, _, _, h => by simpa [reach] using h
  | _ + 1, _, [], _, h => by simpa [reach] using h
  | fuel + 1, seen, x :: xs, b, h => by
    simp only [reach]
    apply reach_mono m fuel
    rw [contains_foldl_insert]
    exact .inr h

/-- With fuel, the walk sees its first frontier. -/
theorem reach_frontier (m : NatMap Block) {fuel : Nat} (hf : 0 < fuel) (seen : NatSet) {frontier : List Nat}
    {b : Nat} (hb : b ∈ frontier) : (reach m fuel seen frontier).contains b = true := by
  obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  cases frontier with
  | nil => simp at hb
  | cons x xs =>
    simp only [reach]
    apply reach_mono m fuel
    rw [contains_foldl_insert]
    by_cases hs : seen.contains b = true
    · exact .inr hs
    · left
      rw [List.mem_filter]
      exact ⟨hb, by simp only [Bool.not_eq_true] at hs; simp [hs]⟩

/-- Every root is reachable. -/
theorem reachable_root (p : Program) {roots : List Nat} {b : Nat} (hb : b ∈ roots) :
    (reachable p roots).contains b = true :=
  reach_frontier _ (by omega) _ (List.mem_cons_of_mem _ hb)

/-- An accepted order places every root. -/
theorem root_placed {p : Program} {s : Shape} {o : Order} (sound : OrderSound p s o) {b : Nat} (hb : b ∈ s.roots) :
    b ∈ o.flatten :=
  sound.reachable b (reachable_root p hb)

/-- Tunnelling does not read the entry. -/
theorem tunnel_withEntry (p : Program) (b : BlockId) : tunnel { p with entry := b } = { tunnel p with entry := b } :=
  rfl

/-- **Layout transports a safe run from any root**: a run of the stacked
program started at root `b` becomes a run of the laid-out program started
at `b`'s new number, with the same final mask, at most as many steps and at
least `1/(blocks + 1)` as many, ending in related machines. -/
theorem transport_at {runtime : Runtime} {cs cq : Checked} {s : Shape} {o : Order} {q : Program}
    {pos : NatMap Nat} (h : Layout.run (tunnel cs.program) s o = .ok (q, pos)) (hq : cq.program = q)
    {b : Nat} (hroot : b ∈ s.roots) {cs' cq' : Checked}
    (hcs : cs'.program = { cs.program with entry := UInt32.ofNat b })
    (hcq : cq'.program = { q with entry := renum o.flatten (UInt32.ofNat b) })
    {n : Nat} {holes holes' : Holes} {core₀ : Core} {m₁ : Machine}
    (steps : SafeSteps runtime cs' n holes (Machine.initial cs' core₀) holes' m₁) :
    ∃ n' mt m₁', SafeSteps runtime cq' n' holes (Machine.initial cq' core₀) holes' m₁' ∧
      n' ≤ n ∧ n ≤ (cs.program.blocks.size + 1) * n' ∧
      (∃ k, TRel cs'.program k m₁ mt) ∧ LRel (tunnel cs'.program) o.flatten holes' mt m₁' := by
  obtain ⟨nt, k, mt, stepsT, relT, hle, hbound⟩ := tunnel_run (c' := tunnelChecked cs') rfl steps
  obtain ⟨setup, sound⟩ := setup_of_run (tunnelChecked cs).valid h (hq ▸ cq.valid)
  have hplaced := root_placed sound hroot
  have hbsz : b < (tunnel cs.program).blocks.size := sound.inRange b hplaced
  have hsmall : (tunnel cs.program).blocks.size < 2 ^ 32 := by
    have := (wellFormed_iff (tunnel cs.program)).1 (tunnelChecked cs).valid
    exact this.2.1
  have hbn : (UInt32.ofNat b).toNat = b := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have htun : (tunnelChecked cs').program = { tunnel cs.program with entry := UInt32.ofNat b } := by
    simp only [tunnelChecked, hcs, tunnel_withEntry]
  have setup' : Setup (tunnelChecked cs').program cq'.program o.flatten := by
    rw [htun, hcq]
    exact { wf := htun ▸ (tunnelChecked cs').valid
            nodup := setup.nodup
            inRange := setup.inRange
            closed := setup.closed
            program := by rw [setup.program]; rfl
            small := setup.small }
  have hentry : (tunnelChecked cs').program.entry.toNat ∈ o.flatten := by
    rw [htun]
    show (UInt32.ofNat b).toNat ∈ o.flatten
    rw [hbn]
    exact hplaced
  obtain ⟨m₁', stepsQ, relL⟩ := lin_safeSteps rfl rfl setup' stepsT (lin_initial rfl rfl setup' hentry core₀ holes)
  have hsz : (tunnelChecked cs').program.blocks.size = cs.program.blocks.size := by
    simp [tunnelChecked, hcs, tunnel]
  refine ⟨nt, mt, m₁', stepsQ, hle, ?_, ⟨k, relT⟩, relL⟩
  have : cs'.program.blocks.size = cs.program.blocks.size := by rw [hcs]
  rw [← this]
  exact hbound

end IxCC.X86.Layout.Proof
