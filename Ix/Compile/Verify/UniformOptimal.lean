import Ix.Compile.Verify.UniformSearch

/-!
# Stage 4: the component cost and its decompositions

The semantic cost `compCost` of a component (its roots, its certain-stored
entries and the entries of a member set), its relation to the uniform length
(`ulen`), and its modularity over separated groups of members.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (Desc)

/-! ## Hash sets, sorted merges, partitions -/

theorem hashSet_foldl_contains (l : List Nat) (s : Std.HashSet Nat) (t : Nat) :
    (l.foldl (fun s x => s.insert x) s).contains t = (s.contains t || decide (t ∈ l)) := by
  induction l generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    by_cases hx : x = t
    · subst hx; simp
    · have : (x == t) = false := by simpa using hx
      simp only [this, Bool.false_or, List.mem_cons]
      by_cases ht : t ∈ xs
      · simp [ht]
      · have : t ≠ x := fun h => hx h.symm
        simp [ht, this]

theorem hashSet_ofArray_contains (arr : Array Nat) (t : Nat) :
    (arr.foldl (·.insert ·) ({} : Std.HashSet Nat)).contains t = decide (t ∈ arr.toList) := by
  rw [← Array.foldl_toList]
  have := hashSet_foldl_contains arr.toList {} t
  simp only [Std.HashSet.contains_empty, Bool.false_or] at this
  exact this

theorem mergeSorted_perm (a b : Array Nat) :
    (mergeSorted a b).toList.Perm (a.toList ++ b.toList) := by
  unfold mergeSorted
  rw [List.toList_toArray]
  exact List.mergeSort_perm _ _

theorem mergeSorted_sorted (a b : Array Nat) :
    (mergeSorted a b).toList.Pairwise (· ≤ ·) := by
  unfold mergeSorted
  rw [List.toList_toArray]
  have := List.pairwise_mergeSort (le := fun x y : Nat => decide (x ≤ y))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (a.toList ++ b.toList)
  exact this.imp (fun h => by simpa using h)

theorem partitionCheck_perm {und : Array Nat} {groups : Array (Array Nat)}
    (h : partitionCheck und groups = true) :
    (groups.toList.flatMap (·.toList)).Perm und.toList := by
  unfold partitionCheck at h
  have he := of_decide_eq_true (by simpa using h)
  have h1 := (List.mergeSort_perm (groups.toList.flatMap (·.toList))
    (fun x y => decide (x ≤ y))).symm
  have h2 := List.mergeSort_perm und.toList (fun x y => decide (x ≤ y))
  rw [he] at h1
  exact h1.trans h2

/-! ## The component cost -/

/-- Availability of a stored member list `V` over the certain-stored terms. -/
def availOf (opaq : Array Bool) (V : List Nat) : Nat → Bool :=
  fun u => opaq[u]! || decide (u ∈ V)

/-- **The component cost** of a member list `V` (stored and available): the
costs of the component's roots, its certain-stored entries and `V`'s entries. -/
def compCost (dag : Dag) (w : Nat) (opaq : Array Bool) (rootsC storedInC V : List Nat) : Nat :=
  (rootsC.map (uCost (Prep.ofDag dag) w (availOf opaq V))).sum +
    (storedInC.map (uInl (Prep.ofDag dag) w (availOf opaq V))).sum +
    (V.map (uInl (Prep.ofDag dag) w (availOf opaq V))).sum

theorem availOf_perm (opaq : Array Bool) {V V' : List Nat} (h : V.Perm V') :
    availOf opaq V = availOf opaq V' := by
  funext u; simp only [availOf, h.mem_iff]

theorem compCost_perm {dag : Dag} {w : Nat} {opaq : Array Bool} {rootsC storedInC : List Nat}
    {V V' : List Nat} (h : V.Perm V') :
    compCost dag w opaq rootsC storedInC V = compCost dag w opaq rootsC storedInC V' := by
  unfold compCost
  rw [availOf_perm opaq h, (h.map _).sum_nat]

theorem availOf_append (opaq : Array Bool) (V V' : List Nat) (u : Nat) :
    availOf opaq (V ++ V') u = (availOf opaq V u || decide (u ∈ V')) := by
  simp only [availOf, List.mem_append]
  by_cases h1 : u ∈ V <;> by_cases h2 : u ∈ V' <;> simp [h1, h2]

/-- **Modularity of the component cost.** Adding the member lists `D` and
`S` to `I` changes the component cost by the sum of adding each, when every
opaque term is opaque in the four availabilities and no available non-opaque
term reaches both `S` and `D` along non-opaque paths. -/
theorem compCost_modular {dag : Dag} (hwf : DagWF dag) (w : Nat) (opaq : Array Bool)
    (rootsC storedInC : List Nat) (hrc : ∀ r ∈ rootsC, r < dag.size)
    (hsc : ∀ c ∈ storedInC, c < dag.size) (O : Nat → Bool) {I D S : List Nat}
    (hin : ∀ t ∈ I ++ D ++ S, t < dag.size)
    (hop : ∀ X : List Nat, (X = I ∨ X = I ++ D ∨ X = I ++ S ∨ X = I ++ D ++ S) →
      OpaqueOn (Prep.ofDag dag) w O (availOf opaq X))
    (hDO : ∀ x ∈ D, O x = false) (hSO : ∀ x ∈ S, O x = false)
    (hsep : ∀ v, v < dag.size → availOf opaq (I ++ D ++ S) v = true → O v = false →
      Unreached (Prep.ofDag dag) O (fun y => decide (y ∈ S)) v ∨
        Unreached (Prep.ofDag dag) O (fun y => decide (y ∈ D)) v) :
    compCost dag w opaq rootsC storedInC (I ++ D ++ S) + compCost dag w opaq rootsC storedInC I =
      compCost dag w opaq rootsC storedInC (I ++ D) +
        compCost dag w opaq rootsC storedInC (I ++ S) := by
  have hp := prepWF_ofDag hwf
  let A0 := availOf opaq I
  let Z1 : Nat → Bool := fun y => decide (y ∈ S)
  let Z2 : Nat → Bool := fun y => decide (y ∈ D)
  have e1 : availOf opaq (I ++ S) = addAvail A0 Z1 := by
    funext u; simp only [availOf_append, addAvail, A0, Z1]
  have e2 : availOf opaq (I ++ D) = addAvail A0 Z2 := by
    funext u; simp only [availOf_append, addAvail, A0, Z2]
  have e12 : availOf opaq (I ++ D ++ S) = addAvail (addAvail A0 Z1) Z2 := by
    funext u; simp only [availOf_append, addAvail, A0, Z1, Z2]
    cases availOf opaq I u <;> cases decide (u ∈ D) <;> cases decide (u ∈ S) <;> rfl
  have h0 := hop I (Or.inl rfl)
  have h1 : OpaqueOn (Prep.ofDag dag) w O (addAvail A0 Z1) := by
    rw [← e1]; exact hop _ (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : OpaqueOn (Prep.ofDag dag) w O (addAvail A0 Z2) := by
    rw [← e2]; exact hop _ (Or.inr (Or.inl rfl))
  have h12 : OpaqueOn (Prep.ofDag dag) w O (addAvail (addAvail A0 Z1) Z2) := by
    rw [← e12]; exact hop _ (Or.inr (Or.inr (Or.inr rfl)))
  have hsep' : ∀ v, v < (Prep.ofDag dag).dag.size → addAvail (addAvail A0 Z1) Z2 v = true →
      O v = false → Unreached (Prep.ofDag dag) O Z1 v ∨ Unreached (Prep.ofDag dag) O Z2 v := by
    intro v hv hav hO
    rw [← e12] at hav
    exact hsep v hv hav hO
  have hmod := hp.uCost_modular w O A0 Z1 Z2 h0 h1 h2 h12 hsep'
  have hlocD : ∀ t ∈ D, uInl (Prep.ofDag dag) w (addAvail (addAvail A0 Z1) Z2) t =
      uInl (Prep.ofDag dag) w (addAvail A0 Z2) t := by
    intro t ht
    have htn := hin t (by simp [ht])
    have hav : availOf opaq (I ++ D ++ S) t = true := by simp [availOf, ht]
    rcases hsep t htn hav (hDO t ht) with hu | hu
    · have hagree : ∀ v, NReach (Prep.ofDag dag) O t v →
          addAvail (addAvail A0 Z1) Z2 v = addAvail A0 Z2 v := by
        intro v hv
        have := hu v hv
        simp only [addAvail, Z1] at this ⊢
        rw [this]
        simp
      exact (hp.uCost_local w O t (by rw [ofDag_dag]; exact htn) _ _ h12 h2 hagree).2
    · exact absurd (hu t .refl) (by simp [ht])
  have hlocS : ∀ t ∈ S, uInl (Prep.ofDag dag) w (addAvail (addAvail A0 Z1) Z2) t =
      uInl (Prep.ofDag dag) w (addAvail A0 Z1) t := by
    intro t ht
    have htn := hin t (by simp [ht])
    have hav : availOf opaq (I ++ D ++ S) t = true := by simp [availOf, ht]
    rcases hsep t htn hav (hSO t ht) with hu | hu
    · exact absurd (hu t .refl) (by simp [ht])
    · exact (hp.uCost_local w O t (by rw [ofDag_dag]; exact htn) _ _ h12 h1
        (agree_of_unreached hu)).2
  unfold compCost
  rw [e1, e2, e12]
  simp only [List.map_append, List.sum_append]
  have hI := congrArg List.sum (List.map_congr_left (l := I) fun t ht =>
    (hmod t (by rw [ofDag_dag]; exact hin t (by simp [ht]))).2)
  have hr := congrArg List.sum (List.map_congr_left (l := rootsC) fun r hr =>
    (hmod r (by rw [ofDag_dag]; exact hrc r hr)).1)
  have hc := congrArg List.sum (List.map_congr_left (l := storedInC) fun c hc =>
    (hmod c (by rw [ofDag_dag]; exact hsc c hc)).2)
  simp only [sum_map_add'] at hI hr hc
  rw [List.map_congr_left hlocD, List.map_congr_left hlocS]
  simp only [A0] at hI hr hc ⊢
  omega

/-! ## The component cost is the component's part of the uniform length -/

theorem uInl_desc_local {dag : Dag} (hwf : DagWF dag) (w : Nat) {A B : Nat → Bool} {y : Nat}
    (hy : y < dag.size) (hag : ∀ v, Desc dag y v → A v = B v) :
    uInl (Prep.ofDag dag) w A y = uInl (Prep.ofDag dag) w B y := by
  have hp := prepWF_ofDag hwf
  let O : Nat → Bool := fun _ => false
  have hOA : ∀ (C : Nat → Bool), OpaqueOn (Prep.ofDag dag) w O C := fun C u _ hu => by
    simp [O] at hu
  exact (hp.uCost_local w O y hy A B (hOA A) (hOA B)
    (fun v hv => hag v (NReach.desc hwf hy hv))).2

theorem sum_filter_split (f : Nat → Nat) (q : Nat → Bool) :
    ∀ l : List Nat, (l.map f).sum = ((l.filter q).map f).sum + ((l.filter (!q ·)).map f).sum
  | [] => rfl
  | x :: xs => by
    have := sum_filter_split f q xs
    cases hx : q x <;> simp [List.filter_cons, hx] <;> omega

theorem availOf_eq_mem {opaq : Array Bool} {cs : List Nat} (hcs : ∀ u, opaq[u]! = decide (u ∈ cs))
    (V : List Nat) : availOf opaq V = fun u => decide (u ∈ cs ++ V) := by
  funext u; simp only [availOf, hcs, List.mem_append]
  by_cases h1 : u ∈ cs <;> by_cases h2 : u ∈ V <;> simp [h1, h2]

/-- **The component cost is the component's part of the length.** With
`opaq` the certain-stored list `cs`, adding a list `V` of the component's
members to `cs` changes the uniform length (without the count's `Tag0`) by the
change of the component cost. -/
theorem ulen_compCost {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) {opaq : Array Bool} {cs : List Nat}
    (hcs : ∀ u, opaq[u]! = decide (u ∈ cs)) (hcsn : cs.Nodup) (hcsb : ∀ c ∈ cs, c < dag.size)
    (members : Array Nat) {V : List Nat} (hV : ∀ t ∈ V, t ∈ members.toList) :
    ulen dag w roots (cs ++ V) + tag0Size cs.length +
        compCost dag w opaq
          (roots.toList.filter ((markTable dag.size
            (upClosure dag ((markTable dag.size members)[·]!)))[·]!))
          ((upClosure dag ((markTable dag.size members)[·]!)).toList.filter (opaq[·]!)) [] =
      ulen dag w roots cs + tag0Size (cs ++ V).length +
        compCost dag w opaq
          (roots.toList.filter ((markTable dag.size
            (upClosure dag ((markTable dag.size members)[·]!)))[·]!))
          ((upClosure dag ((markTable dag.size members)[·]!)).toList.filter (opaq[·]!)) V := by
  generalize hclo : upClosure dag ((markTable dag.size members)[·]!) = clo
  have hclo_mem : ∀ t, t ∈ clo.toList ↔ t < dag.size ∧
      ∃ m, (markTable dag.size members)[m]! = true ∧ Desc dag t m := by
    intro t; rw [← hclo]; exact mem_upClosure hwf _ t
  let inC : Nat → Bool := ((markTable dag.size clo)[·]!)
  have hinC : ∀ t, inC t = true ↔ t ∈ clo.toList := by
    intro t
    show (markTable dag.size clo)[t]! = true ↔ _
    rw [markTable_spec, Array.mem_toList_iff]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, ((hclo_mem t).mp (Array.mem_toList_iff.mpr h)).1⟩
  -- terms outside the closure do not see `V`
  have hout : ∀ t, t < dag.size → inC t = false →
      ∀ v, Desc dag t v → availOf opaq V v = availOf opaq [] v := by
    intro t ht hc v hv
    simp only [availOf, List.not_mem_nil, decide_false, Bool.or_false]
    by_cases hvV : v ∈ V
    · exfalso
      have hvm := hV v hvV
      have hvn : v < dag.size := Nat.lt_of_le_of_lt (Desc.le_of_wf hwf hv ht) ht
      have : t ∈ clo.toList := (hclo_mem t).mpr ⟨ht, v,
        (markTable_spec _ _ _).mpr ⟨Array.mem_toList_iff.mp hvm, hvn⟩, hv⟩
      rw [← hinC] at this
      rw [this] at hc; cases hc
    · simp [hvV]
  have hcsC : (cs.filter inC).Perm (clo.toList.filter (opaq[·]!)) := by
    have hclon : clo.toList.Nodup := by
      rw [← hclo]
      exact (upClosure_sorted _ _).imp (fun h => Nat.ne_of_lt h)
    apply (List.perm_ext_iff_of_nodup (List.Nodup.sublist (List.filter_sublist) hcsn)
      (List.Nodup.sublist (List.filter_sublist) hclon)).mpr
    intro t
    simp only [List.mem_filter, hinC, hcs, decide_eq_true_eq]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have e0 : (fun y => decide (y ∈ cs)) = availOf opaq [] := by
    rw [availOf_eq_mem hcs [], List.append_nil]
  unfold ulen uniformCost compCost
  rw [← availOf_eq_mem hcs V, e0]
  simp only [List.map_append, List.sum_append, List.length_append]
  -- split the roots and the certain-stored entries by the closure
  rw [sum_filter_split (uCost (Prep.ofDag dag) w (availOf opaq V)) inC roots.toList,
    sum_filter_split (uCost (Prep.ofDag dag) w (availOf opaq [])) inC roots.toList,
    sum_filter_split (uInl (Prep.ofDag dag) w (availOf opaq V)) inC cs,
    sum_filter_split (uInl (Prep.ofDag dag) w (availOf opaq [])) inC cs,
    (hcsC.map _).sum_nat, (hcsC.map _).sum_nat]
  have hr : ((roots.toList.filter (!inC ·)).map (uCost (Prep.ofDag dag) w (availOf opaq V))).sum =
      ((roots.toList.filter (!inC ·)).map (uCost (Prep.ofDag dag) w (availOf opaq []))).sum := by
    congr 1
    apply List.map_congr_left
    intro r hr
    rw [List.mem_filter] at hr
    have hrn := hroots r hr.1
    exact uCost_desc_local hwf w hrn (hout r hrn (by simpa using hr.2))
  have hc : ((cs.filter (!inC ·)).map (uInl (Prep.ofDag dag) w (availOf opaq V))).sum =
      ((cs.filter (!inC ·)).map (uInl (Prep.ofDag dag) w (availOf opaq []))).sum := by
    congr 1
    apply List.map_congr_left
    intro c hc
    rw [List.mem_filter] at hc
    have hcn := hcsb c hc.1
    exact uInl_desc_local hwf w hcn (hout c hcn (by simpa using hc.2))
  rw [hr, hc]
  simp only [inC, List.map_nil, List.sum_nil] at *
  omega

/-! ## The global classification -/

/-- The search candidates. -/
def ucand (dag : Dag) (roots : Array Nat) (w : Nat) : Array Bool :=
  searchCandidates (Prep.ofDag dag) (graphFacts dag roots) w

/-- The classification at threshold `θ`. -/
def ucls (dag : Dag) (roots : Array Nat) (w : Nat) (θ : _root_.Int) : Array UClass :=
  classifyWith (Prep.ofDag dag) (graphFacts dag roots) w
    (uniformBounds (Prep.ofDag dag) w (ucand dag roots w)) (visibleCounts dag roots (ucand dag roots w)) θ

theorem ulen_perm {dag : Dag} {w : Nat} {roots : Array Nat} {Y Y' : List Nat} (h : Y.Perm Y') :
    ulen dag w roots Y = ulen dag w roots Y' := by
  unfold ulen uniformCost
  have hm : (fun y => decide (y ∈ Y)) = (fun y => decide (y ∈ Y')) := by
    funext y; simp only [h.mem_iff]
  rw [hm, h.length_eq, (h.map _).sum_nat]

/-- **Splitting off a component.** Adding a list `V` of a component's members
to `cs ++ R` (`R` uncertain terms of other components) changes the uniform
length (without the count's `Tag0`) by the change of the component cost. -/
theorem ulen_split_component {dag : Dag} (hwf : DagWF dag) (roots : Array Nat)
    (hroots : ∀ r ∈ roots.toList, r < dag.size) (w : Nat) (θ : _root_.Int) (hθ : 1 ≤ θ)
    {opaq : Array Bool} {cs : List Nat}
    (hcs : ∀ u, opaq[u]! = decide (u ∈ cs)) (hcsn : cs.Nodup)
    (hcsc : ∀ t ∈ cs, t < dag.size ∧ (ucls dag roots w θ)[t]! = .certainStored)
    (members : Array Nat) (comp : Nat → Nat) (i : Nat)
    (hcomp : ∀ a b, a < dag.size → (ucls dag roots w θ)[a]! = .uncertain →
      (ucls dag roots w θ)[b]! = .uncertain → NReach (Prep.ofDag dag) (opaq[·]!) a b →
      comp a = comp b)
    {V R : List Nat}
    (hV : ∀ t ∈ V, t ∈ members.toList ∧ t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain ∧
      comp t = i)
    (hR : ∀ t ∈ R, t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain ∧ comp t ≠ i) :
    ulen dag w roots (cs ++ V ++ R) + tag0Size (cs ++ R).length +
        compCost dag w opaq
          (roots.toList.filter ((markTable dag.size
            (upClosure dag ((markTable dag.size members)[·]!)))[·]!))
          ((upClosure dag ((markTable dag.size members)[·]!)).toList.filter (opaq[·]!)) [] =
      ulen dag w roots (cs ++ R) + tag0Size (cs ++ V ++ R).length +
        compCost dag w opaq
          (roots.toList.filter ((markTable dag.size
            (upClosure dag ((markTable dag.size members)[·]!)))[·]!))
          ((upClosure dag ((markTable dag.size members)[·]!)).toList.filter (opaq[·]!)) V := by
  have hO : (opaq[·]!) = (fun y => decide (y ∈ cs)) := by funext y; exact hcs y
  have hcm := components_modular hwf roots hroots w θ hθ (cs := cs) (z1 := V) (z2 := R)
    (fun t ht => hcsc t ht)
    (fun t ht => by
      rcases List.mem_append.mp ht with h | h
      · exact ⟨(hV t h).2.1, (hV t h).2.2.1⟩
      · exact ⟨(hR t h).1, (hR t h).2.1⟩)
    comp
    (fun a b ha hb hab => by
      have han : a < dag.size := by
        rcases List.mem_append.mp ha with h | h
        · exact (hV a h).2.1
        · exact (hR a h).1
      have hua : (ucls dag roots w θ)[a]! = .uncertain := by
        rcases List.mem_append.mp ha with h | h
        · exact (hV a h).2.2.1
        · exact (hR a h).2.1
      have hub : (ucls dag roots w θ)[b]! = .uncertain := by
        rcases List.mem_append.mp hb with h | h
        · exact (hV b h).2.2.1
        · exact (hR b h).2.1
      rw [← hO] at hab
      exact hcomp a b han hua hub hab)
    (fun a ha b hb => by rw [(hV a ha).2.2.2]; exact fun h => (hR b hb).2.2 h.symm)
  have huc := ulen_compCost hwf roots hroots w hcs hcsn (fun c hc => (hcsc c hc).1) members
    (V := V) (fun t ht => (hV t ht).1)
  omega

end Ix.Compile.Verify.UniformModel
