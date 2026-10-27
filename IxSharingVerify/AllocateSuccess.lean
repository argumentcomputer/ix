import IxSharingVerify.KahnOrderSpec
import IxSharingVerify.PinnedOrderSpec
import IxSharingVerify.BudgetMono
import IxC.Kernel.Audit.Axioms

/-!
# The first tier never refuses

The slot allocation first searches for the first tier. Its closures refuse
a repeated stored term and a body reference to a later entry; its branch and
bound refuses when its fuel or its state budget runs out. On a duplicate-free
table whose bodies only reference earlier entries, neither closure check
fires, the fuel always suffices and some state budget covers the search
(`firstTier_ok`).
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact

/-- A left fold succeeds when every step succeeds from a state reached
along a prefix, given a condition on the term against that prefix. -/
theorem foldlM_prefix_ok {σ ε : Type} (f : σ → Nat → Except ε σ) (P : List Nat → σ → Prop)
    (Q : List Nat → Nat → Prop)
    (step : ∀ pre t s, P pre s → Q pre t → ∃ s', f s t = .ok s' ∧ P (pre ++ [t]) s') :
    ∀ (l pre : List Nat) (s : σ), P pre s → (∀ a b t, l = a ++ t :: b → Q (pre ++ a) t) →
      ∃ out, l.foldlM f s = .ok out
  | [], _, s, _, _ => ⟨s, rfl⟩
  | t :: rest, pre, s, hp, hq => by
    obtain ⟨s', hs', hp'⟩ := step pre t s hp (by simpa using hq [] rest t rfl)
    obtain ⟨out, hout⟩ := foldlM_prefix_ok f P Q step rest (pre ++ [t]) s' hp' (by
      intro a b t' same
      have := hq (t :: a) b t' (by rw [same]; rfl)
      simpa [List.append_assoc] using this)
    exact ⟨out, by rw [List.foldlM_cons, hs']; exact hout⟩

theorem checkInternal_true' {b : Bool} (msg : String) (h : b = true) :
    checkInternal b msg = .ok () := by
  subst h
  rfl

/-- **The first-tier closures never refuse** a duplicate-free order whose
dependencies come before their users. -/
theorem tierClosures_ok (topo : Array Nat) (deps : Nat → List Nat) (cap : Nat)
    (nodup : topo.toList.Nodup)
    (back : ∀ (a b : List Nat) (t : Nat), topo.toList = a ++ t :: b → ∀ d ∈ deps t, d ∈ a) :
    ∃ cl, tierClosures topo deps cap = .ok cl := by
  unfold tierClosures
  rw [← Array.foldlM_toList]
  refine foldlM_prefix_ok _ (fun pre (cl : Std.HashMap Nat (Option (List Nat))) =>
      ∀ x, cl.contains x = true ↔ x ∈ pre)
    (fun pre t => t ∉ pre ∧ ∀ d ∈ deps t, d ∈ pre) ?_ topo.toList [] {} ?_ ?_
  · intro pre t cl inv ⟨fresh, ready⟩
    have c1 : (!cl.contains t) = true := by
      cases h : cl.contains t with
      | false => rfl
      | true => exact absurd ((inv t).mp h) fresh
    have c2 : ((deps t).all cl.contains) = true := by
      rw [List.all_eq_true]
      intro d hd
      exact (inv d).mpr (ready d hd)
    rw [checkInternal_true' _ c1, checkInternal_true' _ c2]
    refine ⟨_, rfl, ?_⟩
    · intro x
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, inv x, List.mem_append,
        List.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inr h.symm
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h.symm
  · intro x
    simp
  · intro a b t same
    simp only [List.nil_append]
    refine ⟨?_, back a b t same⟩
    rw [same] at nodup
    intro inA
    have := (List.nodup_append.mp nodup).2.2 t inA t List.mem_cons_self
    exact this rfl

/-- **The first-tier search never refuses** with fuel above the remaining
items and a state budget of `2 ^ fuel` above its count; it visits fewer. -/
theorem tierDfs_ok (items : Array Nat) (weight : Nat → Nat) (closure : Nat → Option (List Nat))
    (cap : Nat) (limits : Limits) :
    ∀ (fuel pos cur : Nat) (inF : List Nat) (excluded : Std.HashSet Nat) (st : TierState),
      items.size - pos < fuel → st.states + 2 ^ fuel ≤ limits.maxStates →
      ∃ st', tierDfs items weight closure cap limits fuel pos cur inF excluded st = .ok st' ∧
        st'.states < st.states + 2 ^ fuel := by
  intro fuel
  induction fuel with
  | zero => intro pos cur inF excluded st h; omega
  | succ fuel ih =>
    intro pos cur inF excluded st remaining room
    have pow : 2 ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by rw [Nat.pow_succ]; omega
    have pos1 : 1 ≤ 2 ^ fuel := Nat.one_le_two_pow
    rw [tierDfs.eq_2, ite_eq_right (show ¬ st.states + 1 > limits.maxStates by omega)]
    dsimp only
    split
    · exact ⟨_, rfl, by simp only; omega⟩
    · split
      · exact ⟨_, rfl, by simp only; omega⟩
      · rename_i _ notEnd
        split
        · obtain ⟨st', h', lt'⟩ := ih (pos + 1) cur inF excluded { st with states := st.states + 1 }
            (by omega) (by simp only; omega)
          exact ⟨st', h', by simp only at lt'; omega⟩
        · cases hc : closure items[pos]! with
          | none =>
            obtain ⟨st', h', lt'⟩ := ih (pos + 1) cur inF (excluded.insert items[pos]!)
              { st with states := st.states + 1 } (by omega) (by simp only; omega)
            exact ⟨st', h', by simp only at lt'; omega⟩
          | some c =>
            dsimp only
            split
            · obtain ⟨mid, hmid, ltMid⟩ := ih (pos + 1) _ _ excluded
                { st with states := st.states + 1 } (by omega) (by simp only; omega)
              rw [Budget.bind_ok_eq hmid]
              simp only at ltMid
              obtain ⟨st', h', lt'⟩ := ih (pos + 1) cur inF (excluded.insert items[pos]!) mid
                (by omega) (by omega)
              exact ⟨st', h', by omega⟩
            · obtain ⟨st', h', lt'⟩ := ih (pos + 1) cur inF (excluded.insert items[pos]!)
                { st with states := st.states + 1 } (by omega) (by simp only; omega)
              exact ⟨st', h', by simp only at lt'; omega⟩

/-- **The first tier never refuses** on a duplicate-free order whose
dependencies come before their users. -/
theorem firstTier_ok (topo : Array Nat) (weight : Nat → Nat) (deps : Nat → List Nat) (cap : Nat)
    (nodup : topo.toList.Nodup)
    (back : ∀ (a b : List Nat) (t : Nat), topo.toList = a ++ t :: b → ∀ d ∈ deps t, d ∈ a) :
    ∃ limits out, firstTier topo weight deps cap limits = .ok out := by
  obtain ⟨cl, hcl⟩ := tierClosures_ok topo deps cap nodup back
  let items := (topo.toList.mergeSort (tierOrder weight)).toArray
  let limits : Limits := { maxStates := 2 ^ (items.size + 2) }
  obtain ⟨st, hst, -⟩ := tierDfs_ok items weight (fun t => cl.getD t none) cap limits
    (items.size + 2) 0 0 [] {} {} (by omega) (by simp [limits])
  refine ⟨limits, ?_⟩
  unfold firstTier
  rw [Budget.bind_ok_eq hcl]
  try dsimp only
  rw [Budget.bind_ok_eq hst]
  try dsimp only
  split <;> exact ⟨_, rfl⟩

/-- `respectsDeps` accepts a duplicate-free order that places every
dependency before its user. -/
theorem respectsDeps_ok {order : Array Nat} {deps : Nat → List Nat} (nodup : order.toList.Nodup)
    (resp : ∀ k (hk : k < order.size), ∀ d ∈ deps order[k], ∃ j, j < k ∧ order[j]? = some d) :
    respectsDeps order deps = true := by
  unfold respectsDeps
  simp only
  rw [Array.all_eq_true']
  intro x hx
  have hti := Array.mem_zipIdx_iff_getElem?.mp hx
  obtain ⟨hi, hxt⟩ := Array.getElem?_eq_some_iff.mp hti
  rw [List.all_eq_true]
  intro d hd
  rw [← hxt] at hd
  obtain ⟨j, hj, hjd⟩ := resp x.2 hi d hd
  obtain ⟨hjs, rfl⟩ := Array.getElem?_eq_some_iff.mp hjd
  have pos : (order.zipIdx.foldl (fun m (y : Nat × Nat) => m.insert y.1 y.2)
      ({} : Std.HashMap Nat Nat)).get? order[j] = some j := by
    rw [← Array.foldl_toList, Array.toList_zipIdx]
    apply foldl_insert_get_mem _ _ (by rw [List.zipIdx_map_fst]; exact nodup)
    have : (order[j], j) ∈ order.zipIdx := Array.mem_zipIdx_iff_getElem?.mpr (by simp [hjs])
    rw [← Array.mem_toList_iff, Array.toList_zipIdx] at this
    exact this
  rw [pos]
  simp [hj]

/-- The entry at the length of a prefix. -/
theorem getElem_prefix {order : Array Nat} {a b : List Nat} {t : Nat} (same : order.toList = a ++ t :: b) :
    ∃ h : a.length < order.size, order[a.length] = t := by
  have len := congrArg List.length same
  simp only [Array.length_toList, List.length_append, List.length_cons] at len
  refine ⟨by omega, ?_⟩
  rw [← Array.getElem_toList, List.getElem_of_eq same]
  simp

/-- Every body reference of the phase-1 table is to an earlier entry. -/
theorem allocate_back {dag : Dag} {order1 : Array Nat} {entries1 : Array Ixon.Expr}
    (deps : ∀ i (hi : i < order1.size), ∀ d ∈ (tierDeps order1 entries1).getD order1[i] [],
      ∃ j, j < i ∧ order1[j]? = some d ∧ Ix.Sharing.Verify.SharingExact.Below dag order1[i] d) :
    ∀ (a b : List Nat) (t : Nat), order1.toList = a ++ t :: b →
      ∀ d ∈ (tierDeps order1 entries1).getD t [], d ∈ a := by
  intro a b t same d hd
  obtain ⟨hi, tAt⟩ := getElem_prefix same
  obtain ⟨j, hj, hjd, _⟩ := deps a.length hi d (by rw [tAt]; exact hd)
  obtain ⟨hjs, rfl⟩ := Array.getElem?_eq_some_iff.mp hjd
  rw [← Array.getElem_toList, List.getElem_of_eq same, List.getElem_append_left hj]
  exact List.getElem_mem _

/-- The slot allocation succeeds under every budget under which its first
tier does, on a duplicate-free table of DAG terms whose bodies only
reference earlier entries below them. -/
theorem allocate_of_firstTier (layout : ShareLayout) {dag : Dag}
    (hwf : Ix.Sharing.Verify.UniformModel.DagWF dag)
    (deg : Array Nat) {order1 : Array Nat} (entries1 roots1 : Array Ixon.Expr)
    (nodup : order1.toList.Nodup) (inDag : ∀ t ∈ order1.toList, t < dag.size)
    (deps : ∀ i (hi : i < order1.size), ∀ d ∈ (tierDeps order1 entries1).getD order1[i] [],
      ∃ j, j < i ∧ order1[j]? = some d ∧ Ix.Sharing.Verify.SharingExact.Below dag order1[i] d)
    {first : Limits} {tier : Array Nat} {states : Nat}
    (ft : firstTier order1 (fun t => (tierWeights order1 entries1 roots1).getD t 0)
      (fun t => (tierDeps order1 entries1).getD t []) (min 8 order1.size) first = .ok (tier, states)) :
    ∃ a, allocate layout first dag deg order1 entries1 roots1 = .ok a := by
  let weight := fun t => (tierWeights order1 entries1 roots1).getD t 0
  let dep := fun t => (tierDeps order1 entries1).getD t []
  have depFacts : ∀ t ∈ order1.toList, ∀ d ∈ dep t, d ∈ order1.toList ∧
      Ix.Sharing.Verify.SharingExact.Below dag t d := by
    intro t ht d hd
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp ht)
    obtain ⟨j, _, hjd, below⟩ := deps i hi d hd
    exact ⟨Array.mem_toList_iff.mpr (Array.mem_of_getElem? hjd), below⟩
  obtain ⟨⟨tierNodup, tierIn, tierClosed, -⟩, -, -, -⟩ := firstTier_spec ft
  have storedPerm : (order1.toList.mergeSort (· ≤ ·)).toArray.toList.Perm order1.toList := by
    simpa using List.mergeSort_perm order1.toList (· ≤ ·)
  have storedNodup := storedPerm.nodup_iff.mpr nodup
  let stored := (order1.toList.mergeSort (· ≤ ·)).toArray
  let rest := stored.filter (!tier.contains ·)
  have restMem : ∀ x, x ∈ rest.toList ↔ x ∈ order1.toList ∧ x ∉ tier.toList := by
    intro x
    simp only [rest, Array.toList_filter, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      Array.contains_eq_mem, decide_eq_false_iff_not, Array.mem_toList_iff]
    rw [← Array.mem_toList_iff, storedPerm.mem_iff]
    simp
  have restNodup : rest.toList.Nodup := by
    simp only [rest, Array.toList_filter]
    exact storedNodup.filter _
  have acyclic : ∀ t ∈ rest.toList, ∀ d ∈ dep t, d ∈ rest.toList → d < t := by
    intro t ht d hd _
    exact Ix.Sharing.Verify.Pinned.below_lt hwf (depFacts t ((restMem t).mp ht).1 d hd).2
  obtain ⟨kahnPerm, kahnResp⟩ := kahnOrder_spec weight dep rest restNodup acyclic
  have tierInDag : ∀ s ∈ tier.toList, s < dag.size := fun s hs => inDag s (tierIn s hs)
  let pinned := pinnedOrder dag deg tier
  have pinnedPerm := Ix.Sharing.Verify.UniformModel.pinnedOrder_perm dag deg tier
  let order2 := pinned ++ kahnOrder weight dep rest
  have order2Perm : order2.toList.Perm order1.toList := by
    simp only [order2, Array.toList_append]
    refine (pinnedPerm.append kahnPerm).trans ?_
    rw [List.perm_ext_iff_of_nodup ?_ nodup]
    · intro x
      rw [List.mem_append, restMem]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact tierIn x h
        · exact h
      · intro h
        by_cases ht : x ∈ tier.toList
        · exact Or.inl ht
        · exact Or.inr ⟨h, ht⟩
    · rw [List.nodup_append]
      exact ⟨tierNodup, restNodup, fun a ha b hb same => ((restMem b).mp hb).2 (same ▸ ha)⟩
  have sortedEq : ((order2.toList.mergeSort (· ≤ ·)).toArray == stored) = true := by
    apply beq_iff_eq.mpr
    apply Array.toList_inj.mp
    simp only [stored]
    apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b))
    · intro a b _ _ h1 h2
      simp only [decide_eq_true_eq] at h1 h2
      omega
    · exact List.pairwise_mergeSort (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
    · exact List.pairwise_mergeSort (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
    · exact ((List.mergeSort_perm _ _).trans order2Perm).trans (List.mergeSort_perm _ _).symm
  have order2Resp : ∀ k (hk : k < order2.size), ∀ d ∈ dep order2[k],
      ∃ j, j < k ∧ order2[j]? = some d := by
    intro k hk d hd
    by_cases inPinned : k < pinned.size
    · have hp : (pinnedOrder dag deg tier).size = pinned.size := rfl
      have atK : order2[k] = pinned[k] := Array.getElem_append_left inPinned
      rw [atK] at hd
      have kTier : pinned[k] ∈ tier.toList := pinnedPerm.subset (Array.getElem_mem_toList inPinned)
      have dTier : d ∈ tier.toList := tierClosed _ kTier d hd
      obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp (pinnedPerm.symm.subset dTier))
      have below := (depFacts _ (tierIn _ kTier) _ hd).2
      have jk := Ix.Sharing.Verify.Pinned.pinnedOrder_backward hwf deg tier tierInDag tierNodup
        k j inPinned hj below
      exact ⟨j, jk, by rw [Array.getElem?_eq_getElem (by simp [order2]; omega),
        Array.getElem_append_left hj]⟩
    · have hp : (pinnedOrder dag deg tier).size = pinned.size := rfl
      have kk : k - pinned.size < (kahnOrder weight dep rest).size := by
        simp only [order2, Array.size_append] at hk
        omega
      have atK : order2[k] = (kahnOrder weight dep rest)[k - pinned.size] :=
        Array.getElem_append_right (by omega)
      rw [atK] at hd
      have kRest : (kahnOrder weight dep rest)[k - pinned.size] ∈ rest.toList :=
        kahnPerm.subset (Array.getElem_mem_toList kk)
      have dOrder := (depFacts _ ((restMem _).mp kRest).1 d hd).1
      by_cases dTier : d ∈ tier.toList
      · obtain ⟨j, hj, rfl⟩ :=
          Array.getElem_of_mem (Array.mem_toList_iff.mp (pinnedPerm.symm.subset dTier))
        exact ⟨j, by omega, by rw [Array.getElem?_eq_getElem (by simp [order2]; omega),
          Array.getElem_append_left hj]⟩
      · obtain ⟨j, hj, hjd⟩ := kahnResp _ kk d hd ((restMem d).mpr ⟨dOrder, dTier⟩)
        obtain ⟨hjs, hjv⟩ := Array.getElem?_eq_some_iff.mp hjd
        refine ⟨pinned.size + j, by omega, ?_⟩
        rw [Array.getElem?_eq_getElem (by simp [order2]; omega), Array.getElem_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        rw [hjv]
  have order1Resp : ∀ k (hk : k < order1.size), ∀ d ∈ dep order1[k],
      ∃ j, j < k ∧ order1[j]? = some d := by
    intro k hk d hd
    obtain ⟨j, hj, hjd, _⟩ := deps k hk d hd
    exact ⟨j, hj, hjd⟩
  unfold allocate
  dsimp only
  rw [Budget.bind_ok_eq ft]
  try dsimp only
  rw [checkInternal_true' _ sortedEq]
  split
  · rw [checkInternal_true' _ (respectsDeps_ok nodup order1Resp)]
    exact ⟨_, rfl⟩
  · rw [checkInternal_true' _ (respectsDeps_ok (order2Perm.nodup_iff.mpr nodup) order2Resp)]
    exact ⟨_, rfl⟩

/-- **The slot allocation never refuses** a duplicate-free table of DAG
terms whose bodies only reference earlier entries below them. -/
theorem allocate_ok (layout : ShareLayout) {dag : Dag} (hwf : Ix.Sharing.Verify.UniformModel.DagWF dag)
    (deg : Array Nat) {order1 : Array Nat} (entries1 roots1 : Array Ixon.Expr)
    (nodup : order1.toList.Nodup) (inDag : ∀ t ∈ order1.toList, t < dag.size)
    (deps : ∀ i (hi : i < order1.size), ∀ d ∈ (tierDeps order1 entries1).getD order1[i] [],
      ∃ j, j < i ∧ order1[j]? = some d ∧ Ix.Sharing.Verify.SharingExact.Below dag order1[i] d) :
    ∃ limits a, allocate layout limits dag deg order1 entries1 roots1 = .ok a := by
  obtain ⟨first, ⟨tier, states⟩, ft⟩ := firstTier_ok order1 _ _ (min 8 order1.size) nodup
    (allocate_back deps)
  exact ⟨first, allocate_of_firstTier layout hwf deg entries1 roots1 nodup inDag deps ft⟩

end Ix.Sharing.Verify.Tiered

#guard_kernel_axioms Ix.Sharing.Verify.Tiered.tierClosures_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Tiered.firstTier_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Tiered.allocate_ok [propext, Classical.choice, Quot.sound]
