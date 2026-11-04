import IxSharingVerify.AllocateSuccess
import IxC.Kernel.Audit.Axioms

/-!
# The first-tier search visits polynomially many states

`tierDfs` decides the items in order. An item already chosen is skipped;
any other is included (its closure joins the chosen set, when no excluded
term is in it and the set stays within `cap`) and then excluded. Every
inclusion adds at least the item itself, so no path of the search includes
more than `cap` times, and the subtree with `r` items left and room for `k`
more terms has at most `(r + 1)^(k + 1)` nodes. The search on `m` items
therefore visits at most `(m + 1)^(cap + 1)` states, and with the production
first tier of at most eight entries at most `(m + 1)^9`; under every state
budget of that size it succeeds (`firstTier_within`, `allocate_within`).
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact

theorem succ_pow_ge (r : Nat) : ∀ k, 1 ≤ k → r ^ k + 1 ≤ (r + 1) ^ k
  | 0, h => absurd h (by decide)
  | k + 1, _ => by
    rcases Nat.eq_zero_or_pos k with rfl | pos
    · simp
    · have ih := succ_pow_ge r k pos
      rw [Nat.pow_succ, Nat.pow_succ]
      have grow := Nat.mul_le_mul_right (r + 1) ih
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul] at grow
      omega

/-- Skipping or excluding an item: one node above a subtree with one item less. -/
theorem skip_le (r k : Nat) : 1 + r ^ (k + 1) ≤ (r + 1) ^ (k + 1) := by
  have := succ_pow_ge r (k + 1) (by omega)
  omega

/-- Including and then excluding an item: one node above two subtrees with
one item less, the first with less room. -/
theorem branch_le (r k : Nat) (room : 1 ≤ k) : 1 + r ^ k + r ^ (k + 1) ≤ (r + 1) ^ (k + 1) := by
  have up : r ^ k ≤ (r + 1) ^ k := Nat.pow_le_pow_left (by omega) k
  have grow := succ_pow_ge r k room
  rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_add, Nat.mul_one]
  have := Nat.mul_le_mul_right r up
  omega

/-- **The first-tier search visits at most `(r + 1)^(k + 1)` states** below
a node with `r` items left and room for `k` more terms, and succeeds under
every state budget that covers them. -/
theorem tierDfs_within (items : Array Nat) (weight : Nat → Nat)
    (closure : Nat → Option (List Nat)) (cap : Nat) (limits : Limits)
    (self : ∀ t ∈ items.toList, ∀ c, closure t = some c → t ∈ c) :
    ∀ (fuel pos cur : Nat) (inF : List Nat) (excluded : Std.HashSet Nat) (st : TierState),
      items.size - pos < fuel → inF.length ≤ cap →
      st.states + (items.size - pos + 1) ^ (cap - inF.length + 1) ≤ limits.maxStates →
      ∃ st', tierDfs items weight closure cap limits fuel pos cur inF excluded st = .ok st' ∧
        st'.states ≤ st.states + (items.size - pos + 1) ^ (cap - inF.length + 1) := by
  intro fuel
  induction fuel with
  | zero => intro pos cur inF excluded st h; omega
  | succ fuel ih =>
    intro pos cur inF excluded st remaining fits room
    have one : 0 < (items.size - pos + 1) ^ (cap - inF.length + 1) := Nat.pow_pos (by omega)
    rw [tierDfs.eq_2, ite_eq_right (show ¬ st.states + 1 > limits.maxStates by omega)]
    dsimp only
    split
    · exact ⟨_, rfl, by simp only; omega⟩
    · split
      · exact ⟨_, rfl, by simp only; omega⟩
      · rename_i _ notEnd
        have inside : pos < items.size := by omega
        have left : items.size - (pos + 1) + 1 = items.size - pos := by omega
        have skip := skip_le (items.size - pos) (cap - inF.length)
        split
        · obtain ⟨st', h', le'⟩ := ih (pos + 1) cur inF excluded { st with states := st.states + 1 }
            (by omega) fits (by simp only; rw [left]; omega)
          rw [left] at le'
          exact ⟨st', h', by simp only at le'; omega⟩
        · rename_i fresh
          cases hc : closure items[pos]! with
          | none =>
            obtain ⟨st', h', le'⟩ := ih (pos + 1) cur inF (excluded.insert items[pos]!)
              { st with states := st.states + 1 } (by omega) fits (by simp only; rw [left]; omega)
            rw [left] at le'
            exact ⟨st', h', by simp only at le'; omega⟩
          | some c =>
            dsimp only
            split
            · rename_i chosen
              simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at chosen
              have member : items[pos]! ∈ items.toList := by
                rw [getElem!_pos items pos inside]
                exact Array.getElem_mem_toList inside
              have own := self _ member c hc
              have isNew : items[pos]! ∈ c.filter (fun x => !inF.contains x) := by
                rw [List.mem_filter]
                refine ⟨own, ?_⟩
                simpa using fresh
              have grown := List.length_pos_of_mem isNew
              have room1 : 1 ≤ cap - inF.length := by omega
              have smaller := Nat.pow_le_pow_right (show 0 < items.size - pos by omega)
                (show cap - (inF ++ c.filter (fun x => !inF.contains x)).length + 1 ≤
                  cap - inF.length by rw [List.length_append]; omega)
              have branch := branch_le (items.size - pos) (cap - inF.length) room1
              have fitsNew : (inF ++ c.filter (fun x => !inF.contains x)).length ≤ cap := by
                rw [List.length_append]; omega
              obtain ⟨mid, hmid, leMid⟩ := ih (pos + 1)
                ((c.filter (fun x => !inF.contains x)).foldl (fun acc u => acc + weight u) cur)
                (inF ++ c.filter (fun x => !inF.contains x)) excluded
                { st with states := st.states + 1 } (by omega) fitsNew (by simp only; rw [left]; omega)
              rw [Budget.bind_ok_eq hmid]
              simp only at leMid
              rw [left] at leMid
              obtain ⟨st', h', le'⟩ := ih (pos + 1) cur inF (excluded.insert items[pos]!) mid
                (by omega) fits (by rw [left]; omega)
              rw [left] at le'
              exact ⟨st', h', by omega⟩
            · obtain ⟨st', h', le'⟩ := ih (pos + 1) cur inF (excluded.insert items[pos]!)
                { st with states := st.states + 1 } (by omega) fits (by simp only; rw [left]; omega)
              rw [left] at le'
              exact ⟨st', h', by simp only at le'; omega⟩

/-- **The first tier succeeds under every state budget of
`(m + 1)^(cap + 1)`** on `m` stored terms, in a duplicate-free order whose
dependencies come before their users. -/
theorem firstTier_within (topo : Array Nat) (weight : Nat → Nat) (deps : Nat → List Nat)
    (cap : Nat) (nodup : topo.toList.Nodup)
    (back : ∀ (a b : List Nat) (t : Nat), topo.toList = a ++ t :: b → ∀ d ∈ deps t, d ∈ a)
    {limits : Limits} (room : (topo.size + 1) ^ (cap + 1) ≤ limits.maxStates) :
    ∃ out, firstTier topo weight deps cap limits = .ok out := by
  obtain ⟨cl, hcl⟩ := tierClosures_ok topo deps cap nodup back
  obtain ⟨-, closures, -⟩ := tierClosures_spec hcl
  let items := (topo.toList.mergeSort (tierOrder weight)).toArray
  have size : items.size = topo.size := by simp [items, List.length_mergeSort]
  have self : ∀ t ∈ items.toList, ∀ c, (fun t => cl.getD t none) t = some c → t ∈ c := by
    intro t member c hc
    have inTopo : t ∈ topo.toList :=
      (List.mergeSort_perm topo.toList (tierOrder weight)).subset (by simpa [items] using member)
    have entry := closures t inTopo
    simp only at hc
    rw [hc] at entry
    exact (entry.1.2 t).mpr (.refl t)
  obtain ⟨st, hst, -⟩ := tierDfs_within items weight (fun t => cl.getD t none) cap limits self
    (items.size + 2) 0 0 [] {} {} (by omega) (by simp) (by simpa [size] using room)
  unfold firstTier
  rw [Budget.bind_ok_eq hcl]
  try dsimp only
  rw [Budget.bind_ok_eq hst]
  try dsimp only
  split <;> exact ⟨_, rfl⟩

/-- **The slot allocation succeeds under every state budget of
`(m + 1)^9`** on a duplicate-free table of `m` DAG terms whose bodies only
reference earlier entries below them. -/
theorem allocate_within (layout : ShareLayout) {dag : Dag}
    (hwf : Ix.Sharing.Verify.UniformModel.DagWF dag)
    (deg : Array Nat) {order1 : Array Nat} (entries1 roots1 : Array Ixon.Expr)
    (nodup : order1.toList.Nodup) (inDag : ∀ t ∈ order1.toList, t < dag.size)
    (deps : ∀ i (hi : i < order1.size), ∀ d ∈ (tierDeps order1 entries1).getD order1[i] [],
      ∃ j, j < i ∧ order1[j]? = some d ∧ Ix.Sharing.Verify.SharingExact.Below dag order1[i] d)
    {limits : Limits} (room : (order1.size + 1) ^ 9 ≤ limits.maxStates) :
    ∃ a, allocate layout limits dag deg order1 entries1 roots1 = .ok a := by
  obtain ⟨⟨tier, states⟩, ft⟩ := firstTier_within order1
    (fun t => (tierWeights order1 entries1 roots1).getD t 0)
    (fun t => (tierDeps order1 entries1).getD t []) (min 8 order1.size) nodup (allocate_back deps)
    (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) room)
  exact allocate_of_firstTier layout hwf deg entries1 roots1 nodup inDag deps ft

end Ix.Sharing.Verify.Tiered

#guard_kernel_axioms Ix.Sharing.Verify.Tiered.succ_pow_ge [propext, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Tiered.tierDfs_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Tiered.firstTier_within [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Tiered.allocate_within [propext, Classical.choice, Quot.sound]
