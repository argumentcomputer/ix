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
    cases hx : q x <;> simp [hx] <;> omega

theorem availOf_eq_mem {opaq : Array Bool} {cs : List Nat} (hcs : ∀ u, opaq[u]! = decide (u ∈ cs))
    (V : List Nat) : availOf opaq V = fun u => decide (u ∈ cs ++ V) := by
  funext u; simp only [availOf, hcs, List.mem_append]
  by_cases h1 : u ∈ cs <;> by_cases h2 : u ∈ V <;> simp [h1, h2]

/-- **The component cost is the component's part of the length.** With
`opaq` the certain-stored list `cs`, adding a list `V` of the component's
members to `cs` changes the uniform length (without the count's TagN) by the
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
length (without the count's TagN) by the change of the component cost. -/
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

/-! ## The search context of a component -/

/-- What the search context of a component satisfies (established by
`uniformChoose`). -/
structure SCtxWF (dag : Dag) (roots : Array Nat) (w : Nat) (θ : _root_.Int) (cs : List Nat)
    (cx : SCtx) : Prop where
  prep : cx.up.prep = Prep.ofDag dag
  width : cx.up.w = w
  opaq : ∀ u, cx.up.opaq[u]! = decide (u ∈ cs)
  cand : cx.cand = ucand dag roots w
  bounds0 : cx.bounds0 = uniformBounds (Prep.ofDag dag) w (ucand dag roots w)
  vis0 : cx.vis0 = visibleCounts dag roots (ucand dag roots w)
  mem : ∀ t ∈ cx.members.toList, t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain
  memNodup : cx.members.toList.Nodup
  widthCs_size : cx.widthCs.size = dag.size
  widthCs : ∀ u, widthOf cx.widthCs u = if cx.up.opaq[u]! then some cx.up.w else none
  allTrue : cx.allTrue = Array.replicate dag.size true
  baseEv : cx.baseEv = (Prep.ofDag dag).eval cx.widthCs (Array.replicate dag.size true)
  closure : cx.closure = upClosure dag ((markTable dag.size cx.members)[·]!)
  rootsC : cx.rootsC = roots.filter ((markTable dag.size cx.closure)[·]!)
  storedInC : cx.storedInC = cx.closure.filter (cx.up.opaq[·]!)
  theta : cx.theta = θ

/-- The component cost of a context. -/
def scost (cx : SCtx) (dag : Dag) (V : List Nat) : Nat :=
  compCost dag cx.up.w cx.up.opaq cx.rootsC.toList cx.storedInC.toList V

theorem compAvail_eq_availOf {opaq : Array Bool} {members : Array Nat} {V : List Nat}
    (hV : ∀ t ∈ V, t ∈ members.toList) :
    compAvail opaq members (fun t => decide (t ∈ V)) = availOf opaq V := by
  funext u
  simp only [compAvail, availOf]
  by_cases hu : u ∈ V
  · have := Array.mem_toList_iff.mp (hV u hu)
    simp [hu, this]
  · simp [hu]

/-- **`phiE` is the component cost** of the entries it is given, when they are
the available members. -/
theorem phiE_cost {dag : Dag} (hwf : DagWF dag) {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx) (inArr : Array Nat)
    (hin : ∀ t ∈ inArr.toList, t ∈ cx.members.toList) (avail : Nat → Bool)
    (havail : ∀ t, avail t = decide (t ∈ inArr.toList)) :
    (cx.phiE avail inArr).1 = scost cx dag inArr.toList := by
  have hmem : ∀ t ∈ cx.members, t < dag.size :=
    fun t ht => (hcx.mem t (Array.mem_toList_iff.mpr ht)).1
  have hclo := mem_upClosure hwf ((markTable dag.size cx.members)[·]!)
  have hsc : ∀ t ∈ cx.storedInC, t < dag.size := by
    intro t ht
    rw [hcx.storedInC, Array.mem_filter, hcx.closure] at ht
    exact ((hclo t).mp (Array.mem_toList_iff.mpr ht.1)).1
  have havail' : avail = fun t => decide (t ∈ inArr.toList) := funext havail
  rw [phiE_spec hwf hcx.prep hcx.widthCs_size hcx.widthCs hcx.allTrue hcx.baseEv hcx.closure hmem
    hsc avail inArr (fun x hx => hmem x (Array.mem_toList_iff.mp (hin x (Array.mem_toList_iff.mpr hx))))]
  rw [havail', compAvail_eq_availOf hin]
  rfl

/-- **The lower bound of a node.** `phiE` with the undecided members also
available, but only the decided entries paid, is at most the component cost
of every completion. -/
theorem phiE_lower {dag : Dag} (hwf : DagWF dag) {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx) (inArr : Array Nat)
    (U : List Nat) (hin : ∀ t ∈ inArr.toList, t ∈ cx.members.toList)
    (hU : ∀ t ∈ U, t ∈ cx.members.toList) (avail : Nat → Bool)
    (havail : ∀ t, avail t = decide (t ∈ inArr.toList ∨ t ∈ U)) {X : List Nat}
    (hX : ∀ t ∈ X, t ∈ U) :
    (cx.phiE avail inArr).1 ≤ scost cx dag (inArr.toList ++ X) := by
  have hp := prepWF_ofDag hwf
  have hmem : ∀ t ∈ cx.members, t < dag.size :=
    fun t ht => (hcx.mem t (Array.mem_toList_iff.mpr ht)).1
  have hclo := mem_upClosure hwf ((markTable dag.size cx.members)[·]!)
  have hsc : ∀ t ∈ cx.storedInC, t < dag.size := by
    intro t ht
    rw [hcx.storedInC, Array.mem_filter, hcx.closure] at ht
    exact ((hclo t).mp (Array.mem_toList_iff.mpr ht.1)).1
  have hinU : ∀ t ∈ inArr.toList ++ U, t ∈ cx.members.toList := by
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact hin t h
    · exact hU t h
  have havail' : avail = fun t => decide (t ∈ inArr.toList ++ U) := by
    funext t; rw [havail]; simp [List.mem_append]
  rw [phiE_spec hwf hcx.prep hcx.widthCs_size hcx.widthCs hcx.allTrue hcx.baseEv hcx.closure hmem
    hsc avail inArr (fun x hx => hmem x (Array.mem_toList_iff.mp (hin x (Array.mem_toList_iff.mpr hx))))]
  rw [havail', compAvail_eq_availOf hinU]
  unfold scost compCost
  -- more availability lowers every cost
  have hsub : ∀ v, availOf cx.up.opaq (inArr.toList ++ X) v = true →
      availOf cx.up.opaq (inArr.toList ++ U) v = true := by
    intro v hv
    simp only [availOf, Bool.or_eq_true, decide_eq_true_eq, List.mem_append] at hv ⊢
    rcases hv with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hX v h))
  have hlt : ∀ t, t ∈ cx.members.toList → t < (Prep.ofDag dag).dag.size := by
    intro t ht; rw [ofDag_dag]; exact (hcx.mem t ht).1
  have hr := sum_le_sum_of_le cx.rootsC.toList (f := uCost (Prep.ofDag dag) cx.up.w
      (availOf cx.up.opaq (inArr.toList ++ U)))
    (g := uCost (Prep.ofDag dag) cx.up.w (availOf cx.up.opaq (inArr.toList ++ X)))
    (fun r hr => by
      by_cases hrn : r < dag.size
      · exact (hp.costs_antitone cx.up.w hsub (by rw [ofDag_dag]; exact hrn)).1
      · rw [uCost_of_ge _ _ _ (by rw [ofDag_dag]; omega),
          uCost_of_ge _ _ _ (by rw [ofDag_dag]; omega)]
        exact Nat.le_refl 0)
  have hc := sum_le_sum_of_le cx.storedInC.toList (f := uInl (Prep.ofDag dag) cx.up.w
      (availOf cx.up.opaq (inArr.toList ++ U)))
    (g := uInl (Prep.ofDag dag) cx.up.w (availOf cx.up.opaq (inArr.toList ++ X)))
    (fun c hc => (hp.costs_antitone cx.up.w hsub (by
      rw [ofDag_dag]; exact hsc c (Array.mem_toList_iff.mp hc))).2)
  have he := sum_le_sum_of_le inArr.toList (f := uInl (Prep.ofDag dag) cx.up.w
      (availOf cx.up.opaq (inArr.toList ++ U)))
    (g := uInl (Prep.ofDag dag) cx.up.w (availOf cx.up.opaq (inArr.toList ++ X)))
    (fun x hx => (hp.costs_antitone cx.up.w hsub (hlt x (hin x hx))).2)
  simp only [List.map_append, List.sum_append]
  omega

/-! ## Opaque terms of a decided context -/

/-- The maybe-stored set of a decided-out list. -/
def msOf (cand : Array Bool) (O : Array Nat) : Array Bool :=
  O.foldl (fun acc t => acc.set! t false) cand

theorem msOf_spec (cand : Array Bool) (O : Array Nat) (v : Nat) :
    (msOf cand O)[v]! = true ↔ cand[v]! = true ∧ v ∉ O.toList := by
  unfold msOf
  rw [← Array.foldl_toList, foldl_setBang_const]
  by_cases hv : v ∈ O.toList
  · by_cases hs : v < cand.size
    · simp [hv, hs]
    · simp only [hv, hs, and_false, ite_false, not_true_eq_false, and_false, iff_false]
      simp [hs]
  · simp [hv]

theorem opaqueArr_spec (cx : SCtx) (I O : Array Nat) (t : Nat) :
    (cx.opaqueArr I O)[t]! =
      (cx.up.opaq[t]! || (decide (t ∈ I.toList) && decide (t < cx.up.opaq.size) &&
        cx.opaqueUnder (cx.rebound (msOf cx.cand O)) t)) := by
  unfold SCtx.opaqueArr
  rw [← Array.foldl_toList, foldl_setBang_or]
  rfl

/-- **The opaque terms of a decided context are opaque** in every
availability within its maybe-stored set that contains the certain-stored
terms and the decided-stored ones. -/
theorem opaqueArr_opaqueOn {dag : Dag} (hwf : DagWF dag) {roots : Array Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size) {w : Nat} {θ : _root_.Int} (hθ : 1 ≤ θ)
    {cs : List Nat} {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx)
    (hcsc : ∀ t ∈ cs, t < dag.size ∧ (ucls dag roots w θ)[t]! = .certainStored)
    {I O : Array Nat} {A : Nat → Bool}
    (hA : ∀ v, A v = true → (ucand dag roots w)[v]! = true ∧ v ∉ O.toList)
    (hAin : ∀ t ∈ I.toList, A t = true) (hAcs : ∀ t ∈ cs, A t = true) :
    OpaqueOn (Prep.ofDag dag) w ((cx.opaqueArr I O)[·]!) A := by
  have hp := prepWF_ofDag hwf
  intro t ht hO
  rw [ofDag_dag] at ht
  simp only at hO
  rw [opaqueArr_spec] at hO
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hO
  rcases hO with hcs | ⟨⟨htI, _⟩, hun⟩
  · rw [hcx.opaq] at hcs
    have htcs : t ∈ cs := by simpa using hcs
    exact certainStored_opaque hwf roots hroots w θ hθ ht (hcsc t htcs).2 (hAcs t htcs)
      (fun v hv => (hA v hv).1)
  · generalize hmsd : msOf cx.cand O = ms at hun
    have hms : ∀ v : Nat, ms[v]! = true → (ucand dag roots w)[v]! = true := by
      intro v hv
      rw [← hmsd] at hv
      have := (msOf_spec cx.cand O v).mp hv
      rw [hcx.cand] at this
      exact this.1
    have hAms : ∀ v, A v = true → ms[v]! = true := by
      intro v hv
      rw [← hmsd]
      apply (msOf_spec cx.cand O v).mpr
      rw [hcx.cand]
      exact hA v hv
    have hble : BLe (cx.rebound ms) (uniformBounds (Prep.ofDag dag) w ms) := by
      unfold SCtx.rebound
      rw [hcx.prep, hcx.width, hcx.bounds0, ← Array.foldl_toList]
      exact hp.boundsFold_le w cx.area.toList _
        (uniformBounds_antitone (Prep.ofDag dag) w hms) (uniformBounds_size _ _ _)
    have hbs := hp.bounds_sound w ms A hAms t (by rw [ofDag_dag]; exact ht)
    unfold SCtx.opaqueUnder at hun
    rw [hcx.prep, hcx.width] at hun
    refine ⟨hAin t htI, fun hf => ?_, fun hf => ?_⟩
    · have hfb : ((Prep.ofDag dag).family[t]! == .none) = true := by simp [hf]
      rw [ite_eq_left hfb] at hun
      have h1 := (hble t).1
      have h2 := hbs.2.1
      simp only [ge_iff_le, decide_eq_true_eq] at hun
      omega
    · have hfb : ((Prep.ofDag dag).family[t]! == .none) = false := by simpa using hf
      rw [ite_eq_right (by simp [hfb])] at hun
      have h1 := (hble t).2.1
      have h2 := (hbs.2.2 hf).1
      simp only [ge_iff_le, decide_eq_true_eq] at hun
      omega

/-- Certain-stored and uncertain terms are candidates. -/
theorem ucand_of_ucls {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} {t : Nat}
    (ht : t < dag.size)
    (h : (ucls dag roots w θ)[t]! = .certainStored ∨ (ucls dag roots w θ)[t]! = .uncertain) :
    (ucand dag roots w)[t]! = true := by
  have h1 : (ucls dag roots w θ)[t]! ≠ .certainExcluded := by
    rcases h with h | h <;> rw [h] <;> exact fun h => by cases h
  have h2 : (ucls dag roots w θ)[t]! ≠ .lowDegree := by
    rcases h with h | h <;> rw [h] <;> exact fun h => by cases h
  simp only [ucls, classifyWith] at h1 h2
  rw [getElem!_range_map _ (by rw [ofDag_dag]; exact ht)] at h1 h2
  unfold ucand searchCandidates
  rw [getElem!_range_map _ (by rw [ofDag_dag]; exact ht)]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  by_cases hce : certainExcludedTest (Prep.ofDag dag) (graphFacts dag roots) w t = true
  · exact absurd (by rw [ite_eq_left hce]) h1
  · rw [ite_eq_right hce] at h1 h2
    by_cases hdeg : (graphFacts dag roots).deg[t]! < 2
    · exact absurd (by rw [ite_eq_left hdeg]) h2
    · exact ⟨by simpa using hce, by omega⟩

/-- **Groups are modular.** If a group passes the separation check under the
reduced context `(I, O)`, adding a part `S` of the group and a list `D` of
other members (outside the group and the context) to `I` is additive. -/
theorem group_modular {dag : Dag} (hwf : DagWF dag) {roots : Array Nat}
    (hroots : ∀ r ∈ roots.toList, r < dag.size) {w : Nat} {θ : _root_.Int} (hθ : 1 ≤ θ)
    {cs : List Nat} {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx)
    (hcsc : ∀ t ∈ cs, t < dag.size ∧ (ucls dag roots w θ)[t]! = .certainStored)
    {g I O : Array Nat} (hchk : cx.sepCheck g I O = true)
    (hI : ∀ t ∈ I.toList, t ∈ cx.members.toList ∧ t ∉ O.toList)
    (hO : ∀ t ∈ O.toList, t ∈ cx.members.toList)
    {D S : List Nat}
    (hD : ∀ t ∈ D, t ∈ cx.members.toList ∧ t ∉ g.toList ∧ t ∉ I.toList ∧ t ∉ O.toList)
    (hS : ∀ t ∈ S, t ∈ g.toList) :
    scost cx dag (I.toList ++ D ++ S) + scost cx dag I.toList =
      scost cx dag (I.toList ++ D) + scost cx dag (I.toList ++ S) := by
  have hdag : cx.up.prep.dag = dag := by rw [hcx.prep]; rfl
  obtain ⟨ha, hb⟩ := sepCheck_spec (cx := cx) (by rw [hdag]; exact hwf)
    (by rw [hdag, hcx.closure])
    (by intro t ht; rw [hdag]; exact (hcx.mem t (Array.mem_toList_iff.mpr ht)).1) hchk
  rw [hdag] at ha hb
  -- members are uncertain, so not certain-stored
  have hmemcs : ∀ t ∈ cx.members.toList, t ∉ cs := by
    intro t ht hcs
    have h1 := (hcsc t hcs).2
    rw [(hcx.mem t ht).2] at h1
    cases h1
  have hmemcand : ∀ t ∈ cx.members.toList, (ucand dag roots w)[t]! = true :=
    fun t ht => ucand_of_ucls (hcx.mem t ht).1 (Or.inr (hcx.mem t ht).2)
  have hcscand : ∀ t ∈ cs, (ucand dag roots w)[t]! = true :=
    fun t ht => ucand_of_ucls (hcsc t ht).1 (Or.inl (hcsc t ht).2)
  have hgm : ∀ t ∈ g.toList, t ∈ cx.members.toList ∧ t < dag.size ∧ t ∉ I ∧ t ∉ O :=
    fun t ht => ⟨Array.mem_toList_iff.mpr (ha t (Array.mem_toList_iff.mp ht)).1,
      (ha t (Array.mem_toList_iff.mp ht)).2⟩
  have hall : ∀ t ∈ I.toList ++ D ++ S, t ∈ cx.members.toList ∧ t ∉ O.toList := by
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact hI t ht
      · exact ⟨(hD t ht).1, (hD t ht).2.2.2⟩
    · obtain ⟨h1, _, _, h4⟩ := hgm t (hS t ht)
      exact ⟨h1, fun h => h4 (Array.mem_toList_iff.mp h)⟩
  let OR : Nat → Bool := ((cx.opaqueArr I O)[·]!)
  have hORcs : ∀ v, cx.up.opaq[v]! = true → OR v = true := by
    intro v hv
    show (cx.opaqueArr I O)[v]! = true
    rw [opaqueArr_spec, hv, Bool.true_or]
  have hORfalse : ∀ v, v ∉ cs → v ∉ I.toList → OR v = false := by
    intro v h1 h2
    show (cx.opaqueArr I O)[v]! = false
    rw [opaqueArr_spec, hcx.opaq]
    simp [h1, h2]
  have hop : ∀ X : List Nat,
      (X = I.toList ∨ X = I.toList ++ D ∨ X = I.toList ++ S ∨ X = I.toList ++ D ++ S) →
      OpaqueOn (Prep.ofDag dag) w OR (availOf cx.up.opaq X) := by
    intro X hX
    have hXs : ∀ t ∈ X, t ∈ I.toList ++ D ++ S := by
      intro t ht
      rcases hX with rfl | rfl | rfl | rfl
      · simp [ht]
      · rcases List.mem_append.mp ht with h | h <;> simp [h]
      · rcases List.mem_append.mp ht with h | h <;> simp [h]
      · exact ht
    apply opaqueArr_opaqueOn hwf hroots hθ hcx hcsc
    · intro v hv
      simp only [availOf, Bool.or_eq_true, decide_eq_true_eq] at hv
      rcases hv with hv | hv
      · rw [hcx.opaq] at hv
        have hvcs : v ∈ cs := by simpa using hv
        refine ⟨hcscand v hvcs, fun hvO => ?_⟩
        exact hmemcs v (hO v hvO) hvcs
      · obtain ⟨h1, h2⟩ := hall v (hXs v hv)
        exact ⟨hmemcand v h1, h2⟩
    · intro t ht
      simp only [availOf, Bool.or_eq_true, decide_eq_true_eq]
      right
      rcases hX with rfl | rfl | rfl | rfl <;> simp [ht]
    · intro t ht
      simp only [availOf, Bool.or_eq_true, decide_eq_true_eq]
      left
      rw [hcx.opaq]; simp [ht]
  have hmod := compCost_modular hwf w cx.up.opaq cx.rootsC.toList cx.storedInC.toList
    (by
      intro r hr
      rw [hcx.rootsC, Array.toList_filter, List.mem_filter] at hr
      exact hroots r hr.1)
    (by
      intro c hc
      rw [hcx.storedInC, Array.toList_filter, List.mem_filter, hcx.closure] at hc
      exact ((mem_upClosure hwf _ c).mp hc.1).1)
    OR (I := I.toList) (D := D) (S := S)
    (fun t ht => (hcx.mem t (hall t ht).1).1)
    hop
    (fun x hx => hORfalse x (hmemcs x (hD x hx).1) (hD x hx).2.2.1)
    (fun x hx => hORfalse x (hmemcs x (hgm x (hS x hx)).1)
      (fun h => (hgm x (hS x hx)).2.2.1 (Array.mem_toList_iff.mp h)))
    (by
      intro v hv hav hOv
      have hvcs : v ∉ cs := by
        intro h
        have := hORcs v (by rw [hcx.opaq]; simp [h])
        rw [this] at hOv; cases hOv
      have hvX : v ∈ I.toList ++ D ++ S := by
        simp only [availOf, Bool.or_eq_true, decide_eq_true_eq] at hav
        rcases hav with h | h
        · rw [hcx.opaq] at h; exact absurd (by simpa using h) hvcs
        · exact h
      obtain ⟨hvm, hvO⟩ := hall v hvX
      refine Classical.byContradiction (fun hne => ?_)
      simp only [Unreached, not_or, Classical.not_forall] at hne
      obtain ⟨⟨a, haR, haS⟩, ⟨b, hbR, hbD⟩⟩ := hne
      simp only [Bool.not_eq_false, decide_eq_true_eq] at haS hbD
      obtain ⟨hbm, hbg, hbI, hbO⟩ := hD b hbD
      exact hb v (Array.mem_toList_iff.mp hvm) (fun h => hvO (Array.mem_toList_iff.mpr h)) hOv
        a b haR hbR (Array.mem_toList_iff.mp (hS a haS)) (Array.mem_toList_iff.mp hbm)
        (fun h => hbg (Array.mem_toList_iff.mpr h)) (fun h => hbI (Array.mem_toList_iff.mpr h))
        (fun h => hbO (Array.mem_toList_iff.mpr h)))
  unfold scost
  rw [hcx.width]
  exact hmod

/-! ## The global setting and the shape of a minimum -/

/-- The uncertain terms. -/
def uunc (dag : Dag) (roots : Array Nat) (w : Nat) (θ : _root_.Int) : List Nat :=
  (List.range dag.size).filter (fun t => (ucls dag roots w θ)[t]! == .uncertain)

/-- The always-sound certain-stored threshold of `uniformStage`: one more than
the largest growth of the table count's TagN below the number of candidates. -/
def uthetaMax (dag : Dag) (roots : Array Nat) (w : Nat) : _root_.Int :=
  (tag0StepBound ((ucand dag roots w).filter id).size : _root_.Int) + 1

/-- The optimizer's global checks and choices, and the telescope-spine bound
(`SpinesFit`) under which the certain-excluded class is sound. -/
structure GlobalWF (dag : Dag) (roots : Array Nat) (w : Nat) (θ : _root_.Int) (cs : List Nat) :
    Prop where
  wf : DagWF dag
  spines : SpinesFit (Prep.ofDag dag)
  hroots : ∀ r ∈ roots.toList, r < dag.size
  reach : ∀ y, y < dag.size → ∃ r ∈ roots.toList, Desc dag r y
  theta : θ = uthetaMax dag roots w ∨ (θ = 1 ∧ tag0Size ((ucand dag roots w).filter id).size =
    tag0Size ((ucls dag roots w (uthetaMax dag roots w)).filter (· == .certainStored)).size)
  cs : cs = (List.range dag.size).filter (fun t => (ucls dag roots w θ)[t]! == .certainStored)

theorem ucls_eq {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} {t : Nat}
    (ht : t < dag.size) :
    (ucls dag roots w θ)[t]! =
      if certainExcludedTest (Prep.ofDag dag) (graphFacts dag roots) w t then .certainExcluded
      else if (graphFacts dag roots).deg[t]! < 2 then .lowDegree
      else if storedGainWith (Prep.ofDag dag) (uniformBounds (Prep.ofDag dag) w (ucand dag roots w)) w t
          (visibleCounts dag roots (ucand dag roots w)).1[t]!
          (visibleCounts dag roots (ucand dag roots w)).2[t]! ≥ θ then .certainStored
      else .uncertain := by
  simp only [ucls, classifyWith]
  rw [getElem!_range_map _ (by rw [ofDag_dag]; exact ht)]

theorem GlobalWF.mem_cs {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} (hG : GlobalWF dag roots w θ cs) (t : Nat) :
    t ∈ cs ↔ t < dag.size ∧ (ucls dag roots w θ)[t]! = .certainStored := by
  rw [hG.cs, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, uclass_eq_of_beq h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; exact uclass_beq_self _⟩

theorem mem_uunc {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} (t : Nat) :
    t ∈ uunc dag roots w θ ↔ t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain := by
  rw [uunc, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, uclass_eq_of_beq h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; exact uclass_beq_self _⟩

theorem GlobalWF.cs_nodup {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} (hG : GlobalWF dag roots w θ cs) : cs.Nodup := by
  rw [hG.cs]; exact List.nodup_range.sublist List.filter_sublist

theorem uunc_nodup (dag : Dag) (roots : Array Nat) (w : Nat) (θ : _root_.Int) :
    (uunc dag roots w θ).Nodup :=
  List.nodup_range.sublist List.filter_sublist

/-- Certain-stored and uncertain terms have in-degree at least 2. -/
theorem deg_of_ucls {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} {t : Nat}
    (ht : t < dag.size)
    (h : (ucls dag roots w θ)[t]! = .certainStored ∨ (ucls dag roots w θ)[t]! = .uncertain) :
    2 ≤ (graphFacts dag roots).deg[t]! := by
  rw [ucls_eq ht] at h
  by_cases hce : certainExcludedTest (Prep.ofDag dag) (graphFacts dag roots) w t = true
  · rw [ite_eq_left hce] at h; rcases h with h | h <;> cases h
  · rw [ite_eq_right hce] at h
    by_cases hdeg : (graphFacts dag roots).deg[t]! < 2
    · rw [ite_eq_left hdeg] at h; rcases h with h | h <;> cases h
    · omega

/-- The threshold condition of `classify_sound` at a candidate a minimum omits. -/
theorem GlobalWF.theta_ok {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} (hG : GlobalWF dag roots w θ cs) {X : List Nat}
    (hX : IsMinimum dag w roots X) {t : Nat} (htn : t < dag.size)
    (hc : (ucand dag roots w)[t]! = true) (htX : t ∉ X) :
    θ = uthetaMax dag roots w ∨ (θ = 1 ∧ tag0Size (X.length + 1) = tag0Size X.length) := by
  rcases hG.theta with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, threshold_one_sound hG.wf hG.spines roots hG.hroots hG.reach w hX htn h2 hc
      htX⟩

/-- The threshold is at least 1. -/
theorem GlobalWF.one_le_theta {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} (hG : GlobalWF dag roots w θ cs) : 1 ≤ θ := by
  rcases hG.theta with h | ⟨h, _⟩
  · rw [h]; unfold uthetaMax; omega
  · omega

/-- **Every minimum contains the certain-stored terms.** -/
theorem GlobalWF.min_cs {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} (hG : GlobalWF dag roots w θ cs) {X : List Nat}
    (hX : IsMinimum dag w roots X) {t : Nat} (ht : t ∈ cs) : t ∈ X := by
  obtain ⟨htn, hcls⟩ := (hG.mem_cs t).mp ht
  refine Classical.byContradiction (fun htX => ?_)
  have hθ := hG.theta_ok hX htn (ucand_of_ucls htn (Or.inl hcls)) htX
  exact htX ((classify_sound hG.wf hG.spines roots hG.hroots hG.reach w hX htn θ hθ).2 hcls)

/-- **Every term of a minimum is certain-stored or uncertain.** -/
theorem GlobalWF.min_class {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int}
    {cs : List Nat} (hG : GlobalWF dag roots w θ cs) {X : List Nat}
    (hX : IsMinimum dag w roots X) {t : Nat} (ht : t ∈ X) :
    t < dag.size ∧ ((ucls dag roots w θ)[t]! = .certainStored ∨
      (ucls dag roots w θ)[t]! = .uncertain) := by
  obtain ⟨htn, hdeg⟩ := hX.1.2 t ht
  refine ⟨htn, ?_⟩
  rw [ucls_eq htn]
  by_cases hce : certainExcludedTest (Prep.ofDag dag) (graphFacts dag roots) w t = true
  · exfalso
    unfold certainExcludedTest at hce
    simp only [decide_eq_true_eq] at hce
    exact excluded_of_minimum hG.wf hG.spines roots hG.hroots w hX htn hce ht
  · rw [ite_eq_right hce, ite_eq_right (by omega)]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem nodup_app {a b : List Nat} (ha : a.Nodup) (hb : b.Nodup) (hd : ∀ x ∈ a, x ∉ b) :
    (a ++ b).Nodup :=
  List.nodup_append.mpr ⟨ha, hb, fun x hx _y hy hxy => hd x hx (hxy ▸ hy)⟩

theorem strictInc_spec {a : Array Nat} (h : strictInc a = true) : a.toList.Pairwise (· < ·) := by
  unfold strictInc at h
  rw [List.all_eq_true] at h
  have hstep : ∀ j, j + 1 < a.size → a[j]! < a[j + 1]! := by
    intro j hj
    have := h j (List.mem_range.mpr (by omega))
    simp only [decide_eq_true_eq] at this
    exact this hj
  have hlt : ∀ x y, x < y → y < a.size → a[x]! < a[y]! := by
    intro x y hxy hy
    induction y with
    | zero => omega
    | succ y ih =>
      have := hstep y hy
      by_cases hxy' : x = y
      · subst hxy'; exact this
      · exact Nat.lt_trans (ih (by omega) (by omega)) this
  rw [List.pairwise_iff_getElem]
  intro x y hx hy hxy
  simp only [Array.length_toList] at hx hy
  have := hlt x y hxy hy
  rw [arr_getElem!_eq _ hx, arr_getElem!_eq _ hy] at this
  simpa using this

theorem strictInc_nodup {a : Array Nat} (h : strictInc a = true) : a.toList.Nodup :=
  (strictInc_spec h).imp (fun h => Nat.ne_of_lt h)

/-- The closure lists of a context in the form of `ulen_split_component`. -/
theorem SCtxWF.cost_eq {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} {cs : List Nat}
    {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx) (V : List Nat) :
    scost cx dag V = compCost dag w cx.up.opaq
      (roots.toList.filter ((markTable dag.size
        (upClosure dag ((markTable dag.size cx.members)[·]!)))[·]!))
      ((upClosure dag ((markTable dag.size cx.members)[·]!)).toList.filter (cx.up.opaq[·]!)) V := by
  unfold scost
  rw [hcx.width, hcx.rootsC, hcx.storedInC, hcx.closure, Array.toList_filter, Array.toList_filter]

/-- **Replacing a group's part of a minimum.** Under a separated reduced
context `(I, O)` respected by a minimum `Y`, the group part of `Y` costs at
most `slack` more than any other part `S` of the group (otherwise replacing
it by `S` would shorten `Y`). -/
theorem group_rep {dag : Dag} {roots : Array Nat} {w : Nat} {θ : _root_.Int} {cs : List Nat}
    (hG : GlobalWF dag roots w θ cs) {cx : SCtx} (hcx : SCtxWF dag roots w θ cs cx)
    (comp : Nat → Nat) (i : Nat)
    (hcomp : ∀ a b, a < dag.size → (ucls dag roots w θ)[a]! = .uncertain →
      (ucls dag roots w θ)[b]! = .uncertain → NReach (Prep.ofDag dag) (cx.up.opaq[·]!) a b →
      comp a = comp b)
    (hmemi : ∀ t, t < dag.size → (ucls dag roots w θ)[t]! = .uncertain →
      (t ∈ cx.members.toList ↔ comp t = i))
    {g I O : Array Nat} (hchk : cx.sepCheck g I O = true) (hgn : g.toList.Nodup)
    (hIn : I.toList.Nodup)
    (hI : ∀ t ∈ I.toList, t ∈ cx.members.toList ∧ t ∉ O.toList)
    (hO : ∀ t ∈ O.toList, t ∈ cx.members.toList)
    {Y : List Nat} (hY : IsMinimum dag w roots Y)
    (hYI : ∀ t ∈ I.toList, t ∈ Y) (hYO : ∀ t ∈ O.toList, t ∉ Y)
    {S : List Nat} (hS : ∀ t ∈ S, t ∈ g.toList) (hSn : S.Nodup) :
    scost cx dag (I.toList ++ g.toList.filter (· ∈ Y)) ≤
      scost cx dag (I.toList ++ S) +
        (tag0Size (cs.length + (uunc dag roots w θ).length) - tag0Size cs.length) := by
  have hwf := hG.wf
  have hθ1 : 1 ≤ θ := hG.one_le_theta
  have hcsc : ∀ t ∈ cs, t < dag.size ∧ (ucls dag roots w θ)[t]! = .certainStored :=
    fun t ht => (hG.mem_cs t).mp ht
  have hdag : cx.up.prep.dag = dag := by rw [hcx.prep]; rfl
  obtain ⟨ha, _⟩ := sepCheck_spec (cx := cx) (by rw [hdag]; exact hwf)
    (by rw [hdag, hcx.closure])
    (by intro t ht; rw [hdag]; exact (hcx.mem t (Array.mem_toList_iff.mpr ht)).1) hchk
  rw [hdag] at ha
  have hg : ∀ t ∈ g.toList, t ∈ cx.members.toList ∧ t ∉ I.toList ∧ t ∉ O.toList := by
    intro t ht
    obtain ⟨h1, _, h3, h4⟩ := ha t (Array.mem_toList_iff.mp ht)
    exact ⟨Array.mem_toList_iff.mpr h1, fun h => h3 (Array.mem_toList_iff.mp h),
      fun h => h4 (Array.mem_toList_iff.mp h)⟩
  have hmemu : ∀ t ∈ cx.members.toList, t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain :=
    hcx.mem
  have hmemcs : ∀ t ∈ cx.members.toList, t ∉ cs := by
    intro t ht hcs
    have h1 := (hcsc t hcs).2
    rw [(hmemu t ht).2] at h1
    cases h1
  -- the parts of `Y`
  generalize hYgd : g.toList.filter (· ∈ Y) = Yg
  let D := (cx.members.toList.filter (· ∈ Y)).filter (fun t => decide (t ∉ g.toList ∧ t ∉ I.toList))
  let R := Y.filter (fun t => (ucls dag roots w θ)[t]! == .uncertain && comp t != i)
  have hYg : ∀ t ∈ Yg, t ∈ g.toList ∧ t ∈ Y := by
    intro t ht; rw [← hYgd] at ht; simpa using ht
  have hD : ∀ t ∈ D, t ∈ cx.members.toList ∧ t ∈ Y ∧ t ∉ g.toList ∧ t ∉ I.toList := by
    intro t ht; simp only [D, List.mem_filter, decide_eq_true_eq] at ht; exact ⟨ht.1.1, ht.1.2, ht.2⟩
  have hR : ∀ t ∈ R, t ∈ Y ∧ (ucls dag roots w θ)[t]! = .uncertain ∧ comp t ≠ i := by
    intro t ht
    simp only [R, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at ht
    exact ⟨ht.1, uclass_eq_of_beq ht.2.1, ht.2.2⟩
  have hRn : ∀ t ∈ R, t < dag.size := fun t ht => (hY.1.2 t (hR t ht).1).1
  have hRm : ∀ t ∈ R, t ∉ cx.members.toList := fun t ht hm =>
    (hR t ht).2.2 ((hmemi t (hRn t ht) (hR t ht).2.1).mp hm)
  have hRcs : ∀ t ∈ R, t ∉ cs := fun t ht hcs => by
    have := (hcsc t hcs).2; rw [(hR t ht).2.1] at this; cases this
  have hYn := hY.1.1
  have hmn := hcx.memNodup
  -- duplicate-freedom of the rearrangements
  have hDn : D.Nodup := List.Nodup.sublist (List.Sublist.trans List.filter_sublist
    List.filter_sublist) hmn
  have hYgn : Yg.Nodup := by rw [← hYgd]; exact List.Nodup.sublist List.filter_sublist hgn
  have hRnd : R.Nodup := List.Nodup.sublist List.filter_sublist hYn
  have hcsn := hG.cs_nodup
  have hVn : ∀ X : List Nat, X.Nodup → (∀ t ∈ X, t ∈ g.toList) →
      (I.toList ++ D ++ X).Nodup := by
    intro X hXn hXg
    apply nodup_app (nodup_app hIn hDn (fun x hx hxD => (hD x hxD).2.2.2 hx)) hXn
    intro x hx hxX
    rcases List.mem_append.mp hx with h | h
    · exact (hg x (hXg x hxX)).2.1 h
    · exact (hD x h).2.2.1 (hXg x hxX)
  have hVm : ∀ X : List Nat, (∀ t ∈ X, t ∈ g.toList) →
      ∀ t ∈ I.toList ++ D ++ X, t ∈ cx.members.toList := by
    intro X hXg t ht
    rcases List.mem_append.mp ht with h | h
    · rcases List.mem_append.mp h with h | h
      · exact (hI t h).1
      · exact (hD t h).1
    · exact (hg t (hXg t h)).1
  have hYn' : ∀ X : List Nat, X.Nodup → (∀ t ∈ X, t ∈ g.toList) →
      (cs ++ (I.toList ++ D ++ X) ++ R).Nodup := by
    intro X hXn hXg
    apply nodup_app (nodup_app hcsn (hVn X hXn hXg) (fun x hx hxV => hmemcs x (hVm X hXg x hxV) hx))
      hRnd
    intro x hx hxR
    rcases List.mem_append.mp hx with h | h
    · exact hRcs x hxR h
    · exact hRm x hxR (hVm X hXg x h)
  have hnodup1 := hYn' Yg hYgn (fun t ht => (hYg t ht).1)
  -- `Y` as certain-stored, component and other parts
  have hperm : Y.Perm (cs ++ (I.toList ++ D ++ Yg) ++ R) := by
    apply (List.perm_ext_iff_of_nodup hYn ?_).mpr
    · intro t
      constructor
      · intro htY
        obtain ⟨htn, hcl⟩ := hG.min_class hY htY
        rcases hcl with hcl | hcl
        · simp [(hG.mem_cs t).mpr ⟨htn, hcl⟩]
        · by_cases hci : comp t = i
          · have htm := (hmemi t htn hcl).mpr hci
            by_cases htI : t ∈ I.toList
            · simp [htI]
            · by_cases htg : t ∈ g.toList
              · have : t ∈ Yg := by rw [← hYgd]; simp [htg, htY]
                simp [this]
              · have : t ∈ D := by
                  simp only [D, List.mem_filter, decide_eq_true_eq]
                  exact ⟨⟨htm, htY⟩, htg, htI⟩
                simp [this]
          · have : t ∈ R := by
              simp only [R, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq]
              exact ⟨htY, by rw [hcl]; exact uclass_beq_self _, hci⟩
            simp [this]
      · intro ht
        simp only [List.mem_append] at ht
        rcases ht with (h | ((h | h) | h)) | h
        · exact hG.min_cs hY h
        · exact hYI t h
        · exact (hD t h).2.1
        · exact (hYg t h).2
        · exact (hR t h).1
    · exact hnodup1
  -- the replaced set is in the class
  let Y' := cs ++ (I.toList ++ D ++ S) ++ R
  have hY'n : Y'.Nodup := hYn' S hSn hS
  have hY'c : InClass dag roots Y' := by
    refine ⟨hY'n, fun s hs => ?_⟩
    simp only [Y', List.mem_append] at hs
    have hcl : s < dag.size ∧ ((ucls dag roots w θ)[s]! = .certainStored ∨
        (ucls dag roots w θ)[s]! = .uncertain) := by
      rcases hs with (h | h) | h
      · exact ⟨(hcsc s h).1, Or.inl (hcsc s h).2⟩
      · have := hmemu s (hVm S hS s (by rcases h with (h | h) | h <;> simp [h]))
        exact ⟨this.1, Or.inr this.2⟩
      · exact ⟨hRn s h, Or.inr (hR s h).2.1⟩
    exact ⟨hcl.1, deg_of_ucls hcl.1 hcl.2⟩
  have hle : ulen dag w roots (cs ++ (I.toList ++ D ++ Yg) ++ R) ≤ ulen dag w roots Y' := by
    rw [← ulen_perm hperm]; exact hY.2 Y' hY'c
  -- the component's share of each
  have hVfacts : ∀ X : List Nat, (∀ t ∈ X, t ∈ g.toList) → ∀ t ∈ I.toList ++ D ++ X,
      t ∈ cx.members.toList ∧ t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain ∧
        comp t = i := by
    intro X hXg t ht
    have hm := hVm X hXg t ht
    exact ⟨hm, (hmemu t hm).1, (hmemu t hm).2, (hmemi t (hmemu t hm).1 (hmemu t hm).2).mp hm⟩
  have hRfacts : ∀ t ∈ R, t < dag.size ∧ (ucls dag roots w θ)[t]! = .uncertain ∧ comp t ≠ i :=
    fun t ht => ⟨hRn t ht, (hR t ht).2.1, (hR t ht).2.2⟩
  have hs1 := ulen_split_component hwf roots hG.hroots w θ hθ1 hcx.opaq hcsn hcsc cx.members comp i
    hcomp (V := I.toList ++ D ++ Yg) (R := R) (hVfacts Yg (fun t ht => (hYg t ht).1)) hRfacts
  have hs2 := ulen_split_component hwf roots hG.hroots w θ hθ1 hcx.opaq hcsn hcsc cx.members comp i
    hcomp (V := I.toList ++ D ++ S) (R := R) (hVfacts S hS) hRfacts
  have hDfacts : ∀ t ∈ D, t ∈ cx.members.toList ∧ t ∉ g.toList ∧ t ∉ I.toList ∧ t ∉ O.toList :=
    fun t ht => ⟨(hD t ht).1, (hD t ht).2.2.1, (hD t ht).2.2.2,
      fun h => hYO t h (hD t ht).2.1⟩
  have hm1 := group_modular hwf hG.hroots hθ1 hcx hcsc hchk hI hO (D := D) (S := Yg) hDfacts
    (fun t ht => (hYg t ht).1)
  have hm2 := group_modular hwf hG.hroots hθ1 hcx hcsc hchk hI hO (D := D) (S := S) hDfacts hS
  rw [hcx.cost_eq, hcx.cost_eq, hcx.cost_eq, hcx.cost_eq] at hm1 hm2
  rw [hcx.cost_eq, hcx.cost_eq]
  -- the counts lie between `|cs|` and `|cs| + |unc|`
  have hlenY : cs.length ≤ (cs ++ (I.toList ++ D ++ Yg) ++ R).length := by
    simp only [List.length_append]; omega
  have hlenY' : Y'.length ≤ cs.length + (uunc dag roots w θ).length := by
    have hsub : ∀ t ∈ Y', t ∈ cs ++ uunc dag roots w θ := by
      intro t ht
      have := hY'c.2 t ht
      simp only [Y', List.mem_append] at ht
      rcases ht with (h | h) | h
      · simp [h]
      · have hm := hVm S hS t (by rcases h with (h | h) | h <;> simp [h])
        simp [(mem_uunc t).mpr (hmemu t hm)]
      · simp [(mem_uunc t).mpr ⟨hRn t h, (hR t h).2.1⟩]
    have := List.Nodup.length_le_of_subset hY'n hsub
    simpa using this
  have ht1 := tag0Size_mono hlenY
  have ht2 := tag0Size_mono hlenY'
  have ht3 := tag0Size_mono (Nat.le_add_right cs.length (uunc dag roots w θ).length)
  simp only [List.length_append] at ht1 ht2 hs1 hs2 hle
  simp only [Y', List.length_append] at ht2 hle
  omega

end Ix.Compile.Verify.UniformModel
