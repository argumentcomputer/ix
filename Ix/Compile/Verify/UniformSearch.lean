import Ix.Compile.Verify.UniformChecks
import Ix.Compile.Verify.UniformFinal

/-!
# Stage 4: specifications of the component search's checks and tables

The restricted reach-label pass (`reachLabelsOn`) over the members'
ancestors (`upClosure`), the label and mark tables, and what a passing
group separation check (`SCtx.sepCheck`) guarantees. These are proofs about the
implementation module of the same name, `Ix.Sharing.Exact.UniformSearch`;
they extend the namespace `Ix.Compile.Verify.UniformModel`.
-/

namespace Ix.Compile.Verify.UniformModel

open Ix.Sharing.Exact
open Ix.Compile.Verify.SharingExact (Desc child_eq_getElem setBang_getElem!)

/-! ## Folds of `set!` -/

theorem size_setBang {α : Type} (a : Array α) (i : Nat) (v : α) : (a.set! i v).size = a.size := by
  simp [Array.set!]

/-- Setting a constant along a list. -/
theorem foldl_setBang_const {α : Type} [Inhabited α] (v : α) :
    ∀ (l : List Nat) (a : Array α) (x : Nat),
      (l.foldl (fun acc t => acc.set! t v) a)[x]! = if x ∈ l ∧ x < a.size then v else a[x]!
  | [], a, x => by simp
  | t :: l, a, x => by
    rw [List.foldl_cons, foldl_setBang_const v l _ x, size_setBang, setBang_getElem!]
    by_cases hxt : t = x
    · subst hxt
      by_cases hx : t < a.size <;> by_cases hxl : t ∈ l <;> simp [hx, hxl]
    · have : x ≠ t := fun h => hxt h.symm
      simp [hxt, this]

theorem foldl_setBang_const_size {α : Type} (v : α) :
    ∀ (l : List Nat) (a : Array α), (l.foldl (fun acc t => acc.set! t v) a).size = a.size
  | [], _ => rfl
  | t :: l, a => by rw [List.foldl_cons, foldl_setBang_const_size v l, size_setBang]

/-- Or-ing a value into a table along a list. -/
theorem foldl_setBang_or (f : Nat → Bool) :
    ∀ (l : List Nat) (a : Array Bool) (x : Nat),
      (l.foldl (fun acc t => acc.set! t (acc[t]! || f t)) a)[x]! =
        (a[x]! || (decide (x ∈ l) && decide (x < a.size) && f x))
  | [], a, x => by simp
  | t :: l, a, x => by
    rw [List.foldl_cons, foldl_setBang_or f l _ x, size_setBang, setBang_getElem!]
    by_cases hxt : t = x
    · subst hxt
      by_cases hx : t < a.size <;> by_cases hxl : t ∈ l <;> cases a[t]! <;> cases f t <;>
        simp [hx, hxl]
    · have : x ≠ t := fun h => hxt h.symm
      simp [hxt, this]

/-! ## Mark and label tables -/

theorem markTable_spec (n : Nat) (ts : Array Nat) (x : Nat) :
    (markTable n ts)[x]! = true ↔ x ∈ ts ∧ x < n := by
  unfold markTable
  rw [← Array.foldl_toList, foldl_setBang_const]
  by_cases h : x ∈ ts.toList ∧ x < (Array.replicate n false).size
  · rw [ite_eq_left h]
    simp only [Array.size_replicate, Array.mem_toList_iff] at h
    simp [h]
  · rw [ite_eq_right h]
    simp only [Array.size_replicate, Array.mem_toList_iff, not_and] at h
    constructor
    · intro hx
      by_cases hxn : x < n
      · simp [hxn] at hx
      · simp [hxn] at hx
    · rintro ⟨h1, h2⟩; exact absurd h2 (h h1)

theorem sepLabels_spec (n : Nat) (members g inRed outRed : Array Nat) (x : Nat) :
    (sepLabels n members g inRed outRed)[x]! =
      if x < n ∧ x ∉ inRed ∧ x ∉ outRed then
        (if x ∈ g then some 1 else if x ∈ members then some 2 else none)
      else none := by
  unfold sepLabels
  simp only
  rw [← Array.foldl_toList, foldl_setBang_const, ← Array.foldl_toList, foldl_setBang_const,
    ← Array.foldl_toList, foldl_setBang_const]
  simp only [foldl_setBang_const_size, Array.size_replicate,
    Array.toList_append, List.mem_append, Array.mem_toList_iff]
  by_cases hxn : x < n
  · by_cases hio : x ∈ inRed ∨ x ∉ outRed <;> by_cases hi : x ∈ inRed <;> by_cases ho : x ∈ outRed <;>
      by_cases hg : x ∈ g <;> by_cases hm : x ∈ members <;>
      simp_all
  · have : ¬ x < (Array.replicate n (none : Option Nat)).size := by simpa using hxn
    simp [hxn]
    rfl

/-! ## Paths and descendants -/

theorem DagWF.children_size {dag : Dag} (hwf : DagWF dag) {t : Nat} (ht : t < dag.size) :
    (dag.node t).children.size = (dag.node t).head.arity := by
  have := hwf.arity t ht
  rw [← dag_node_eq ht] at this
  exact this

/-- A path avoiding opaque terms is a path. -/
theorem NReach.desc {dag : Dag} (hwf : DagWF dag) {O : Nat → Bool} {y v : Nat}
    (hy : y < dag.size) (h : NReach (Prep.ofDag dag) O y v) : Desc dag y v := by
  induction h with
  | refl => exact .refl _
  | @tail u v hu _ he ih =>
    obtain ⟨k, hk, rfl⟩ := he
    have hun : u < dag.size := Nat.lt_of_le_of_lt (NReach.le_of_wf hwf hu hy) hy
    simp only [ofDag_dag] at hk ⊢
    exact desc_snoc ih (by rw [hwf.children_size hun]; exact hk)

theorem Desc.le_of_wf {dag : Dag} (hwf : DagWF dag) {y v : Nat} (h : Desc dag y v)
    (hy : y < dag.size) : v ≤ y := by
  induction h with
  | refl => exact Nat.le_refl _
  | @child t u k hk _ ih =>
    have hc : (dag.node t).child k < t := by
      rw [child_eq_getElem _ k hk]
      exact hwf.child_lt hy (Array.getElem_mem _)
    have := ih (by omega)
    omega

/-! ## Members and their ancestors -/

/-- The marks of `upClosure`. -/
def upMarks (dag : Dag) (isMember : Nat → Bool) : Array Bool :=
  foldRange (fun (acc : Array Bool) t =>
    acc.set! t (isMember t || (dag.node t).children.any (acc[·]!))) 0 dag.size
    (Array.replicate dag.size false)

theorem upClosure_eq (dag : Dag) (isMember : Nat → Bool) :
    upClosure dag isMember = (Array.range dag.size).filter ((upMarks dag isMember)[·]!) := rfl

/-- The row of `upMarks` at `t`, reading `acc` for the children. -/
def upRow (dag : Dag) (isMember : Nat → Bool) (acc : Array Bool) (t : Nat) : Bool :=
  isMember t || (dag.node t).children.any (acc[·]!)

theorem upRow_congr {dag : Dag} (hwf : DagWF dag) {isMember : Nat → Bool} {a b : Array Bool}
    {t : Nat} (ht : t < dag.size) (h : ∀ c, c < t → a[c]! = b[c]!) :
    upRow dag isMember a t = upRow dag isMember b t := by
  unfold upRow
  congr 1
  apply Bool.eq_iff_iff.mpr
  rw [Array.any_eq_true, Array.any_eq_true]
  constructor <;> rintro ⟨i, hi, hc⟩ <;> refine ⟨i, hi, ?_⟩
  · rw [← h _ (hwf.child_lt ht (Array.getElem_mem _))]; exact hc
  · rw [h _ (hwf.child_lt ht (Array.getElem_mem _))]; exact hc

theorem upMarks_spec {dag : Dag} (hwf : DagWF dag) (isMember : Nat → Bool) {t : Nat}
    (ht : t < dag.size) :
    (upMarks dag isMember)[t]! = upRow dag isMember (upMarks dag isMember) t := by
  have hinv : ∀ m, m ≤ dag.size →
      ((List.range m).foldl (fun acc t => acc.set! t (upRow dag isMember acc t))
          (Array.replicate dag.size false)).size = dag.size ∧
      ∀ t, t < m →
        ((List.range m).foldl (fun acc t => acc.set! t (upRow dag isMember acc t))
            (Array.replicate dag.size false))[t]! =
          upRow dag isMember ((List.range m).foldl
            (fun acc t => acc.set! t (upRow dag isMember acc t))
            (Array.replicate dag.size false)) t := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by simp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hrows⟩ := ih (by omega)
      rw [foldl_range_succ]
      generalize (List.range m).foldl (fun acc t => acc.set! t (upRow dag isMember acc t))
        (Array.replicate dag.size false) = acc at hs hrows
      have keep : ∀ c, c < m → (acc.set! m (upRow dag isMember acc m))[c]! = acc[c]! :=
        fun c hc => setBang_getElem!_ne _ _ (by omega)
      refine ⟨by simp [hs], fun t ht => ?_⟩
      by_cases htm : t = m
      · subst htm
        rw [setBang_getElem!_self _ _ (by omega)]
        exact upRow_congr hwf (by omega) fun c hc => (keep c hc).symm
      · rw [keep t (by omega), hrows t (by omega)]
        exact upRow_congr hwf (by omega) fun c hc => (keep c (by omega)).symm
  unfold upMarks
  rw [foldRange_zero]
  exact (hinv dag.size (Nat.le_refl _)).2 t ht

/-- **A term is marked iff a member lies at or below it.** -/
theorem upMarks_iff {dag : Dag} (hwf : DagWF dag) (isMember : Nat → Bool) :
    ∀ t, t < dag.size →
      ((upMarks dag isMember)[t]! = true ↔ ∃ m, isMember m = true ∧ Desc dag t m) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    rw [upMarks_spec hwf isMember ht]
    unfold upRow
    rw [Bool.or_eq_true, Array.any_eq_true]
    constructor
    · rintro (h | ⟨k, hk, hc⟩)
      · exact ⟨t, h, .refl _⟩
      · have hlt : (dag.node t).children[k] < t := hwf.child_lt ht (Array.getElem_mem _)
        obtain ⟨m, hm, hd⟩ := (ih _ hlt (by omega)).mp hc
        refine ⟨m, hm, .child k hk ?_⟩
        rw [child_eq_getElem _ k hk]
        exact hd
    · rintro ⟨m, hm, hd⟩
      cases hd with
      | refl => exact Or.inl hm
      | child k hk hd =>
        right
        refine ⟨k, hk, ?_⟩
        have hlt : (dag.node t).children[k] < t := hwf.child_lt ht (Array.getElem_mem _)
        rw [child_eq_getElem _ k hk] at hd
        exact (ih _ hlt (by omega)).mpr ⟨m, hm, hd⟩

theorem mem_upClosure {dag : Dag} (hwf : DagWF dag) (isMember : Nat → Bool) (t : Nat) :
    t ∈ (upClosure dag isMember).toList ↔
      t < dag.size ∧ ∃ m, isMember m = true ∧ Desc dag t m := by
  rw [upClosure_eq, Array.mem_toList_iff, Array.mem_filter, Array.mem_range]
  constructor
  · rintro ⟨ht, hm⟩; exact ⟨ht, (upMarks_iff hwf isMember t ht).mp hm⟩
  · rintro ⟨ht, hm⟩; exact ⟨ht, (upMarks_iff hwf isMember t ht).mpr hm⟩

theorem upClosure_sorted (dag : Dag) (isMember : Nat → Bool) :
    (upClosure dag isMember).toList.Pairwise (· < ·) := by
  rw [upClosure_eq, Array.toList_filter, Array.toList_range]
  exact (List.pairwise_lt_range).filter _

/-! ## Restricted reach summaries -/

/-- **The restricted reach summaries allow every reachable label** at the
terms of a strictly increasing `order` that contains every non-opaque child
of its terms reaching a labeled term. -/
theorem reachLabelsOn_allows {dag : Dag} (hwf : DagWF dag) (order : Array Nat)
    (opq : Nat → Bool) (lab : Nat → Option Nat)
    (hsorted : order.toList.Pairwise (· < ·)) (hlt : ∀ t ∈ order.toList, t < dag.size)
    (hclosed : ∀ y ∈ order.toList, ∀ k, k < (dag.node y).head.arity →
      opq ((dag.node y).child k) = false →
      ∀ v ℓ, NReach (Prep.ofDag dag) opq ((dag.node y).child k) v → lab v = some ℓ →
        (dag.node y).child k ∈ order.toList) :
    ∀ y ∈ order.toList, ∀ v, NReach (Prep.ofDag dag) opq y v → ∀ ℓ, lab v = some ℓ →
      Allows (reachLabelsOn dag order opq lab)[y]! ℓ := by
  let Inv (acc : Array (Option (Option Nat))) (P : List Nat) : Prop :=
    ∀ y ∈ P, ∀ v, NReach (Prep.ofDag dag) opq y v → ∀ ℓ, lab v = some ℓ → Allows acc[y]! ℓ
  have key : ∀ (l P : List Nat) (acc : Array (Option (Option Nat))),
      l.Pairwise (· < ·) → (∀ y ∈ P, ∀ x ∈ l, y < x) → (∀ x ∈ l, x < dag.size) →
      acc.size = dag.size →
      (∀ y ∈ l, ∀ k, k < (dag.node y).head.arity → opq ((dag.node y).child k) = false →
        ∀ v ℓ, NReach (Prep.ofDag dag) opq ((dag.node y).child k) v → lab v = some ℓ →
          (dag.node y).child k ∈ P ∨ (dag.node y).child k ∈ l) →
      Inv acc P →
      Inv (l.foldl (fun acc t => acc.set! t (labelRow dag opq lab acc t)) acc) (P ++ l) := by
    intro l
    induction l with
    | nil => intro P acc _ _ _ _ _ h; simpa using h
    | cons x l ih =>
      intro P acc hs hPl hl hsz hcl hinv
      rw [List.foldl_cons]
      have hx : x < dag.size := hl x List.mem_cons_self
      have hxl : ∀ z ∈ l, x < z := (List.pairwise_cons.mp hs).1
      have step : Inv (acc.set! x (labelRow dag opq lab acc x)) (P ++ [x]) := by
        intro y hy v hv ℓ hℓ
        rcases List.mem_append.mp hy with hyP | hyx
        · have hyx : y < x := hPl y hyP x List.mem_cons_self
          rw [setBang_getElem!_ne _ _ (by omega)]
          exact hinv y hyP v hv ℓ hℓ
        · rw [List.mem_singleton] at hyx
          subst hyx
          rw [setBang_getElem!_self _ _ (by omega)]
          unfold labelRow
          rw [← Array.foldl_toList]
          apply allows_foldl
          rcases hv.head with rfl | ⟨k, hk, (⟨hO, rfl⟩ | ⟨hO, hc⟩)⟩
          · left; rw [hℓ]; exact Or.inr rfl
          · right
            simp only [ofDag_dag] at hk hO hℓ ⊢
            refine ⟨(dag.node y).child k, ?_, ?_⟩
            · rw [child_eq_getElem _ k (by rw [hwf.children_size hx]; exact hk)]
              exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
            · rw [ite_eq_left hO, hℓ]; exact Or.inr rfl
          · right
            simp only [ofDag_dag] at hk hO hc ⊢
            have hclt := hwf.childAt_lt hx hk
            refine ⟨(dag.node y).child k, ?_, ?_⟩
            · rw [child_eq_getElem _ k (by rw [hwf.children_size hx]; exact hk)]
              exact Array.mem_toList_iff.mpr (Array.getElem_mem _)
            · rw [ite_eq_right (by simp [hO])]
              rcases hcl y List.mem_cons_self k hk hO v ℓ hc hℓ with hcP | hcl'
              · exact hinv _ hcP v hc ℓ hℓ
              · rcases List.mem_cons.mp hcl' with he | he
                · omega
                · have := hxl _ he; omega
      have := ih (P ++ [x]) (acc.set! x (labelRow dag opq lab acc x)) hs.of_cons
        (fun y hy z hz => by
          rcases List.mem_append.mp hy with hyP | hyx
          · exact hPl y hyP z (List.mem_cons_of_mem _ hz)
          · rw [List.mem_singleton] at hyx; subst hyx; exact hxl z hz)
        (fun z hz => hl z (List.mem_cons_of_mem _ hz))
        (by rw [size_setBang, hsz])
        (fun y hy k hk hO v ℓ hc hℓ => by
          rcases hcl y (List.mem_cons_of_mem _ hy) k hk hO v ℓ hc hℓ with h | h
          · exact Or.inl (List.mem_append_left _ h)
          · rcases List.mem_cons.mp h with h | h
            · exact Or.inl (List.mem_append_right _ (by rw [h]; exact List.mem_singleton_self _))
            · exact Or.inr h)
        step
      simpa using this
  intro y hy v hv ℓ hℓ
  have := key order.toList [] (Array.replicate dag.size none) hsorted (by simp) hlt (by simp)
    (fun y hy k hk hO v ℓ hc hℓ => Or.inr (hclosed y hy k hk hO v ℓ hc hℓ)) (by simp [Inv])
  unfold reachLabelsOn
  rw [← Array.foldl_toList]
  exact this y (by simpa using hy) v hv ℓ hℓ

/-! ## The group separation check -/

/-- **What a passing separation check guarantees.** The group's terms are
members outside the reduced context; and no member that can be stored (not
in `outRed`) and is not opaque under the reduced context reaches, along paths
whose intermediate terms are not opaque, both a group term and a member
outside the group and the context. -/
theorem sepCheck_spec {cx : SCtx} (hwf : DagWF cx.up.prep.dag)
    (hclo : cx.closure =
      upClosure cx.up.prep.dag ((markTable cx.up.prep.dag.size cx.members)[·]!))
    (hmem : ∀ t ∈ cx.members, t < cx.up.prep.dag.size)
    {g inRed outRed : Array Nat} (hchk : cx.sepCheck g inRed outRed = true) :
    (∀ t ∈ g, t ∈ cx.members ∧ t < cx.up.prep.dag.size ∧ t ∉ inRed ∧ t ∉ outRed) ∧
    (∀ v ∈ cx.members, v ∉ outRed → (cx.opaqueArr inRed outRed)[v]! = false →
      ∀ a b, NReach (Prep.ofDag cx.up.prep.dag) ((cx.opaqueArr inRed outRed)[·]!) v a →
        NReach (Prep.ofDag cx.up.prep.dag) ((cx.opaqueArr inRed outRed)[·]!) v b →
        a ∈ g → b ∈ cx.members → b ∉ g → b ∉ inRed → b ∉ outRed → False) := by
  generalize hdag : cx.up.prep.dag = dag at hwf hclo hmem
  have hn : cx.up.prep.dag.size = dag.size := by rw [hdag]
  unfold SCtx.sepCheck at hchk
  simp only [Bool.and_eq_true, Array.all_eq_true'] at hchk
  obtain ⟨hg, hv⟩ := hchk
  rw [hdag] at hv hg
  generalize hO : cx.opaqueArr inRed outRed = O at hv ⊢
  have hga : ∀ t ∈ g, t ∈ cx.members ∧ t < dag.size ∧ t ∉ inRed ∧ t ∉ outRed := by
    intro t ht
    have := hg t ht
    simp only [beq_iff_eq] at this
    obtain ⟨h1, h2⟩ := this
    rw [markTable_spec] at h1
    rw [sepLabels_spec] at h2
    by_cases hc : t < dag.size ∧ t ∉ inRed ∧ t ∉ outRed
    · exact ⟨h1.1, hc⟩
    · rw [ite_eq_right hc] at h2; cases h2
  refine ⟨hga, ?_⟩
  intro v hvm hvo hvO a b ha hb hag hbm hbg hbi hbo
  have hvn := hmem v hvm
  have hbn : b < dag.size := Nat.lt_of_le_of_lt (NReach.le_of_wf hwf hb hvn) hvn
  -- the labels of `a` and `b`
  let lab := sepLabels dag.size cx.members g inRed outRed
  have hla : lab[a]! = some 1 := by
    obtain ⟨_, han, hai, hao⟩ := hga a hag
    show (sepLabels dag.size cx.members g inRed outRed)[a]! = some 1
    rw [sepLabels_spec, ite_eq_left ⟨han, hai, hao⟩, ite_eq_left hag]
  have hlb : lab[b]! = some 2 := by
    show (sepLabels dag.size cx.members g inRed outRed)[b]! = some 2
    rw [sepLabels_spec, ite_eq_left ⟨hbn, hbi, hbo⟩, ite_eq_right hbg, ite_eq_left hbm]
  -- every labeled term is a member
  have hlabm : ∀ x ℓ, lab[x]! = some ℓ → x ∈ cx.members ∧ x < dag.size := by
    intro x ℓ hx
    have hx' : (sepLabels dag.size cx.members g inRed outRed)[x]! = some ℓ := hx
    rw [sepLabels_spec] at hx'
    by_cases hc : x < dag.size ∧ x ∉ inRed ∧ x ∉ outRed
    · rw [ite_eq_left hc] at hx'
      by_cases hxg : x ∈ g
      · exact ⟨(hga x hxg).1, hc.1⟩
      · rw [ite_eq_right hxg] at hx'
        by_cases hxm : x ∈ cx.members
        · exact ⟨hxm, hc.1⟩
        · rw [ite_eq_right hxm] at hx'; cases hx'
    · rw [ite_eq_right hc] at hx'; cases hx'
  -- the closure facts
  let isMem := markTable dag.size cx.members
  have hcl_mem : ∀ t, t ∈ cx.closure.toList ↔ t < dag.size ∧ ∃ m, isMem[m]! = true ∧ Desc dag t m := by
    intro t; rw [hclo]; exact mem_upClosure hwf _ t
  have hvc : v ∈ cx.closure.toList :=
    (hcl_mem v).mpr ⟨hvn, v, (markTable_spec _ _ _).mpr ⟨hvm, hvn⟩, .refl _⟩
  have hallows := reachLabelsOn_allows hwf cx.closure (O[·]!) (lab[·]!)
    (by rw [hclo]; exact upClosure_sorted _ _)
    (fun t ht => ((hcl_mem t).mp ht).1)
    (by
      intro y hy k hk _ x ℓ hx hℓ
      have hyn := ((hcl_mem y).mp hy).1
      have hcn := hwf.childAt_lt hyn hk
      obtain ⟨hxm, hxn⟩ := hlabm x ℓ hℓ
      exact (hcl_mem _).mpr ⟨by omega, x, (markTable_spec _ _ _).mpr ⟨hxm, hxn⟩,
        NReach.desc hwf (by omega) hx⟩)
  have h1 := hallows v hvc a ha 1 hla
  have h2 := hallows v hvc b hb 2 hlb
  have hcheck := hv v hvm
  have hout : (markTable dag.size outRed)[v]! = false := by
    cases h : (markTable dag.size outRed)[v]!
    · rfl
    · exact absurd ((markTable_spec _ _ _).mp h).1 hvo
  rw [hout, hvO] at hcheck
  simp only [Bool.false_or, bne_iff_ne, ne_eq] at hcheck
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact hcheck h1
  · exact hcheck h1
  · exact hcheck h2
  · rw [h1] at h2; cases h2

/-! ## The component evaluation (B2) -/

/-- Availability of a component evaluation: the certain-stored terms and the
available members. -/
def compAvail (opaq : Array Bool) (members : Array Nat) (avail : Nat → Bool) : Nat → Bool :=
  fun u => opaq[u]! || (decide (u ∈ members) && avail u)

theorem widthOf_eq (width : Array (Option Nat)) (u : Nat) : widthOf width u = width[u]! := by
  unfold widthOf
  rw [getElem!_def]
  cases width[u]? <;> rfl

theorem widthFold_size (w : Nat) (avail : Nat → Bool) :
    ∀ (l : List Nat) (a : Array (Option Nat)),
      (l.foldl (fun acc t => if avail t then acc.set! t (some w) else acc) a).size = a.size
  | [], _ => rfl
  | t :: l, a => by
    rw [List.foldl_cons, widthFold_size w avail l]
    split <;> simp

theorem widthFold_spec (w : Nat) (avail : Nat → Bool) :
    ∀ (l : List Nat) (a : Array (Option Nat)) (u : Nat),
      widthOf (l.foldl (fun acc t => if avail t then acc.set! t (some w) else acc) a) u =
        if u ∈ l ∧ avail u = true ∧ u < a.size then some w else widthOf a u
  | [], a, u => by simp
  | t :: l, a, u => by
    rw [List.foldl_cons, widthFold_spec w avail l]
    have hsz : (if avail t = true then a.set! t (some w) else a).size = a.size := by
      split <;> simp
    rw [hsz]
    by_cases hut : u = t
    · subst hut
      by_cases hav : avail u = true
      · simp only [hav, ite_true, widthOf_eq]
        by_cases hu : u < a.size
        · simp [hu]
        · simp [hu]
      · simp [hav]
    · have hw : widthOf (if avail t = true then a.set! t (some w) else a) u = widthOf a u := by
        split
        · rw [widthOf_eq, widthOf_eq, setBang_getElem!_ne _ _ hut]
        · rfl
      simp only [List.mem_cons, hut, false_or, hw]

/-- The model rows of a term agree under availabilities that agree on its
descendants. -/
theorem evalRow_local {dag : Dag} (hwf : DagWF dag) {w : Nat} {A B : Nat → Bool} {st : DictEval}
    {t : Nat} (ht : t < dag.size) (hagree : ∀ v, Desc dag t v → A v = B v)
    (h : EvalRow (Prep.ofDag dag) w A st t) : EvalRow (Prep.ofDag dag) w B st t := by
  have hp := prepWF_ofDag hwf
  let O : Nat → Bool := fun _ => false
  have hOA : ∀ (C : Nat → Bool), OpaqueOn (Prep.ofDag dag) w O C := fun C u _ hu => by
    simp [O] at hu
  have hloc : ∀ y, y < dag.size → (∀ v, Desc dag y v → A v = B v) →
      uCost (Prep.ofDag dag) w A y = uCost (Prep.ofDag dag) w B y := fun y hy hag =>
    (hp.uCost_local w O y hy A B (hOA A) (hOA B)
      (fun v hv => hag v (NReach.desc hwf hy hv))).1
  have hspine : ∀ k, (Prep.ofDag dag).family[t]! ≠ .none → k < (Prep.ofDag dag).spineLen[t]! →
      Desc dag t (spineAt (Prep.ofDag dag) t k) := fun k hf hk =>
    NReach.desc hwf ht (hp.spine_nreach (O := O) ht hf (k := 0) k (Nat.zero_le _) hk
      (fun _ _ _ => rfl))
  obtain ⟨hc, hs⟩ := h
  refine ⟨by rw [hc]; exact hloc t ht hagree, fun hf => ?_⟩
  obtain ⟨hsd, hfa⟩ := hs hf
  refine ⟨?_, ?_⟩
  · rw [hsd]
    apply prefixSides_local
    intro i hi
    obtain ⟨hts, htf, _⟩ := hp.spine_shift ht hf (k := i) hi
    have hfs : (Prep.ofDag dag).family[spineAt (Prep.ofDag dag) t i]! ≠ .none := by
      rw [htf]; exact hf
    obtain ⟨m, hm, he⟩ := hp.side_edge hts hfs
    have hlt := hp.sideAt_lt ht hf hi
    have hd : Desc dag t (sideAt (Prep.ofDag dag) t i) := by
      unfold sideAt
      rw [← he]
      exact desc_snoc (hspine i hf hi) (by rw [hwf.children_size hts]; exact hm)
    exact hloc _ (by omega) (fun v hv => hagree v (hd.trans hv))
  · have hag : ∀ k, k < (Prep.ofDag dag).spineLen[t]! →
        A (spineAt (Prep.ofDag dag) t k) = B (spineAt (Prep.ofDag dag) t k) :=
      fun k hk => hagree _ (hspine k hf hk)
    cases hb : st.below[t]! with
    | none =>
      rw [hb] at hfa
      intro k hk1 hk2
      rw [← hag k hk2]; exact hfa k hk1 hk2
    | some u =>
      rw [hb] at hfa
      obtain ⟨k, hk1, hk2, hu, hau, hnone⟩ := hfa
      refine ⟨k, hk1, hk2, hu, by rw [hu, ← hag k hk2, ← hu]; exact hau, fun k' h1 h2 => ?_⟩
      rw [← hag k' (by omega)]; exact hnone k' h1 h2

theorem evalStep_keep (dag : Dag) (family : Array Family) (spineLen tail : Array Nat)
    (width : Array (Option Nat)) (aff : Array Bool) (st : DictEval) {x t : Nat} (h : t ≠ x) :
    (evalStep dag family spineLen tail width aff st x).cost[t]! = st.cost[t]! ∧
      (evalStep dag family spineLen tail width aff st x).sides[t]! = st.sides[t]! ∧
      (evalStep dag family spineLen tail width aff st x).below[t]! = st.below[t]! := by
  unfold evalStep
  split
  · dsimp only
    split
    · exact ⟨setBang_getElem!_ne _ _ h, rfl, rfl⟩
    · exact ⟨setBang_getElem!_ne _ _ h, setBang_getElem!_ne _ _ h, setBang_getElem!_ne _ _ h⟩
  · exact ⟨rfl, rfl, rfl⟩

theorem evalRow_of_agree {p : Prep} {w : Nat} {A : Nat → Bool} {st st' : DictEval} {t : Nat}
    (h1 : st'.cost[t]! = st.cost[t]!) (h2 : st'.sides[t]! = st.sides[t]!)
    (h3 : st'.below[t]! = st.below[t]!) (h : EvalRow p w A st t) : EvalRow p w A st' t := by
  obtain ⟨hc, hs⟩ := h
  exact ⟨by rw [h1, hc], fun hf => by rw [h2, h3]; exact hs hf⟩

theorem uCost_desc_local {dag : Dag} (hwf : DagWF dag) (w : Nat) {A B : Nat → Bool} {y : Nat}
    (hy : y < dag.size) (hag : ∀ v, Desc dag y v → A v = B v) :
    uCost (Prep.ofDag dag) w A y = uCost (Prep.ofDag dag) w B y := by
  have hp := prepWF_ofDag hwf
  let O : Nat → Bool := fun _ => false
  have hOA : ∀ (C : Nat → Bool), OpaqueOn (Prep.ofDag dag) w O C := fun C u _ hu => by
    simp [O] at hu
  exact (hp.uCost_local w O y hy A B (hOA A) (hOA B)
    (fun v hv => hag v (NReach.desc hwf hy hv))).1

/-- Folding `evalStep` over a list of terms. -/
def evalFold (dag : Dag) (width : Array (Option Nat)) (aff : Array Bool) (l : List Nat)
    (st : DictEval) : DictEval :=
  l.foldl (evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
    (Prep.ofDag dag).tail width aff) st

/-- **Incremental evaluation.** Folding `evalStep` over a strictly increasing
list from an evaluation whose rows are the model rows at every term outside
the list establishes the model rows at every term. -/
theorem evalFold_rows {dag : Dag} (hwf : DagWF dag) {w : Nat} {A : Nat → Bool}
    (width : Array (Option Nat)) (hwidth : ∀ u, widthOf width u = if A u then some w else none)
    (aff : Array Bool) (haff : ∀ t, t < dag.size → aff[t]! = true) :
    ∀ (l : List Nat) (st : DictEval), l.Pairwise (· < ·) → (∀ x ∈ l, x < dag.size) →
      (st.cost.size = dag.size ∧ st.sides.size = dag.size ∧ st.below.size = dag.size) →
      (∀ t, t < dag.size → t ∉ l → EvalRow (Prep.ofDag dag) w A st t) →
      ((evalFold dag width aff l st).cost.size = dag.size ∧
        (evalFold dag width aff l st).sides.size = dag.size ∧
        (evalFold dag width aff l st).below.size = dag.size) ∧
        ∀ t, t < dag.size → EvalRow (Prep.ofDag dag) w A (evalFold dag width aff l st) t
  | [], st, _, _, hsz, hrows => ⟨hsz, fun t ht => hrows t ht List.not_mem_nil⟩
  | x :: l, st, hs, hlt, hsz, hrows => by
    have hx := hlt x List.mem_cons_self
    have hxl : ∀ z ∈ l, x < z := (List.pairwise_cons.mp hs).1
    have hp := prepWF_ofDag hwf
    obtain ⟨hsz', hrows'⟩ := hp.evalStep_spec width hwidth aff st x hx (haff x hx) hsz
      (fun t htx => hrows t (by omega) (by
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · omega
        · have := hxl t h; omega))
    have := evalFold_rows hwf width hwidth aff haff l _ hs.of_cons
      (fun z hz => hlt z (List.mem_cons_of_mem _ hz)) hsz' (fun t ht htl => by
        by_cases htx : t < x + 1
        · exact hrows' t htx
        · have hne : t ≠ x := by omega
          obtain ⟨k1, k2, k3⟩ := evalStep_keep _ _ _ _ width aff st hne
          exact evalRow_of_agree k1 k2 k3 (hrows t ht (by
            intro hm
            rcases List.mem_cons.mp hm with h | h
            · omega
            · exact htl h)))
    unfold evalFold at this ⊢
    rw [List.foldl_cons]
    exact this

theorem inlOf_avail_congr {p : Prep} {w : Nat} {A B : Nat → Bool} {f : Nat → Nat} {x : Nat}
    (h : p.family[x]! ≠ .none → ∀ j, 1 ≤ j → j < p.spineLen[x]! →
      A (spineAt p x j) = B (spineAt p x j)) :
    inlOf p w A f x = inlOf p w B f x := by
  unfold inlOf
  split
  · rfl
  · rename_i hf
    congr 1
    unfold cutCosts
    apply filterMap_congr'
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [h hf j hj.1 (by omega)]

/-- **An entry's body by one more step.** Re-evaluating a term with its own
width removed gives its inline cost. -/
theorem entry_inl {dag : Dag} (hwf : DagWF dag) {w : Nat} {A : Nat → Bool}
    (width : Array (Option Nat)) (hwsz : width.size = dag.size)
    (hwidth : ∀ u, widthOf width u = if A u then some w else none) (ev : DictEval)
    (hsz : ev.cost.size = dag.size ∧ ev.sides.size = dag.size ∧ ev.below.size = dag.size)
    (hrows : ∀ t, t < dag.size → EvalRow (Prep.ofDag dag) w A ev t) {x : Nat} (hx : x < dag.size) :
    (evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
      (Prep.ofDag dag).tail (width.set! x none) (Array.replicate dag.size true) ev x).cost[x]! =
      uInl (Prep.ofDag dag) w A x := by
  have hp := prepWF_ofDag hwf
  let A' : Nat → Bool := fun u => A u && decide (u ≠ x)
  have hwidth' : ∀ u, widthOf (width.set! x none) u = if A' u then some w else none := by
    intro u
    by_cases hux : u = x
    · subst hux
      rw [widthOf_eq, setBang_getElem!_self _ _ (by omega)]
      simp [A']
    · rw [widthOf_eq, setBang_getElem!_ne _ _ hux, ← widthOf_eq, hwidth]
      simp [A', hux]
  have hag : ∀ t, t < x → ∀ v, Desc dag t v → A v = A' v := by
    intro t htx v hv
    have := Desc.le_of_wf hwf hv (by omega)
    have hvx : v ≠ x := by omega
    simp [A', hvx]
  have rows' : ∀ t, t < x → EvalRow (Prep.ofDag dag) w A' ev t :=
    fun t htx => evalRow_local hwf (by omega) (hag t htx) (hrows t (by omega))
  obtain ⟨_, hr⟩ := hp.evalStep_spec (width.set! x none) hwidth' (Array.replicate dag.size true)
    ev x hx (by simp [hx]) hsz rows'
  rw [(hr x (Nat.lt_succ_self x)).1, hp.uCost_eq w A' x hx]
  unfold costOf uInl
  rw [ite_eq_right (by simp [A'])]
  rw [hp.inlOf_congr (avail := A') hx (g := uCost (Prep.ofDag dag) w A) (fun c hc =>
    uCost_desc_local hwf w (Nat.lt_trans hc hx) (fun v hv => (hag c hc v hv).symm))]
  apply inlOf_avail_congr
  intro hf j hj1 hj2
  have := hp.spineAt_lt hx hf hj1 hj2
  have hne : spineAt (Prep.ofDag dag) x j ≠ x := by omega
  simp [A', hne]

theorem replicate_getBang {α : Type} [Inhabited α] {n t : Nat} {v : α} (ht : t < n) :
    (Array.replicate n v)[t]! = v := by
  simp [ht]

/-- The evaluation of a component with `avail` available: the model rows of
`compAvail` at every term. -/
theorem compEval_rows {dag : Dag} (hwf : DagWF dag) (w : Nat) (opaq : Array Bool)
    (members : Array Nat) (hmem : ∀ t ∈ members, t < dag.size) (avail : Nat → Bool)
    (widthCs : Array (Option Nat)) (hwsz : widthCs.size = dag.size)
    (hwcs : ∀ u, widthOf widthCs u = if opaq[u]! then some w else none) :
    let width := members.foldl (fun acc t => if avail t then acc.set! t (some w) else acc) widthCs
    let ev := evalFold dag width (Array.replicate dag.size true)
      (upClosure dag ((markTable dag.size members)[·]!)).toList
      ((Prep.ofDag dag).eval widthCs (Array.replicate dag.size true))
    width.size = dag.size ∧
      (∀ u, widthOf width u = if compAvail opaq members avail u then some w else none) ∧
      (ev.cost.size = dag.size ∧ ev.sides.size = dag.size ∧ ev.below.size = dag.size) ∧
      ∀ t, t < dag.size → EvalRow (Prep.ofDag dag) w (compAvail opaq members avail) ev t := by
  intro width ev
  have hp := prepWF_ofDag hwf
  let A := compAvail opaq members avail
  have hwsz' : width.size = dag.size := by
    show (members.foldl _ widthCs).size = _
    rw [← Array.foldl_toList, widthFold_size, hwsz]
  have hwidth : ∀ u, widthOf width u = if A u then some w else none := by
    intro u
    show widthOf (members.foldl _ widthCs) u = _
    rw [← Array.foldl_toList, widthFold_spec, hwcs]
    simp only [Array.mem_toList_iff, A, compAvail]
    by_cases hum : u ∈ members <;> by_cases hav : avail u = true <;>
      by_cases ho : opaq[u]! = true <;> simp [hum, hav, ho, hwsz, hmem u]
  -- the certain-stored evaluation
  let Acs : Nat → Bool := fun u => opaq[u]!
  have hbrows : ∀ t, t < dag.size → EvalRow (Prep.ofDag dag) w Acs
      ((Prep.ofDag dag).eval widthCs (Array.replicate dag.size true)) t := by
    intro t ht
    exact hp.evalFrom_spec widthCs hwcs (Prep.ofDag dag).empty (ofDag_empty_size dag)
      (Array.replicate dag.size true) (fun t ht => replicate_getBang ht) t ht
  have hbsz := evalFrom_size (Prep.ofDag dag).dag (Prep.ofDag dag).family
    (Prep.ofDag dag).spineLen (Prep.ofDag dag).tail (Prep.ofDag dag).empty widthCs
    (Array.replicate dag.size true)
  obtain ⟨e1, e2, e3⟩ := ofDag_empty_size dag
  rw [e1, e2, e3] at hbsz
  have hclo := mem_upClosure hwf ((markTable dag.size members)[·]!)
  have hfold := evalFold_rows hwf width hwidth (Array.replicate dag.size true)
    (fun t ht => replicate_getBang ht) (upClosure dag ((markTable dag.size members)[·]!)).toList
    ((Prep.ofDag dag).eval widthCs (Array.replicate dag.size true))
    (upClosure_sorted _ _) (fun x hx => ((hclo x).mp hx).1) hbsz
    (fun t ht htc => evalRow_local hwf ht (fun v hv => by
      show Acs v = A v
      simp only [Acs, A, compAvail]
      by_cases hvm : v ∈ members
      · exact absurd ((hclo t).mpr ⟨ht, v, (markTable_spec _ _ _).mpr ⟨hvm, hmem v hvm⟩, hv⟩) htc
      · simp [hvm]) (hbrows t ht))
  exact ⟨hwsz', hwidth, hfold⟩

/-- **The component evaluation (B2).** `phiE` is the model cost of the
component's roots, its certain-stored entries and the entries of `stored`,
with the certain-stored terms and the available members stored. -/
theorem phiE_spec {cx : SCtx} {dag : Dag} (hwf : DagWF dag) (hprep : cx.up.prep = Prep.ofDag dag)
    (hwsz : cx.widthCs.size = dag.size)
    (hwcs : ∀ u, widthOf cx.widthCs u = if cx.up.opaq[u]! then some cx.up.w else none)
    (hall : cx.allTrue = Array.replicate dag.size true)
    (hbase : cx.baseEv = (Prep.ofDag dag).eval cx.widthCs (Array.replicate dag.size true))
    (hclo : cx.closure = upClosure dag ((markTable dag.size cx.members)[·]!))
    (hmem : ∀ t ∈ cx.members, t < dag.size) (hsc : ∀ t ∈ cx.storedInC, t < dag.size)
    (avail : Nat → Bool) (stored : Array Nat) (hst : ∀ x ∈ stored, x < dag.size) :
    (cx.phiE avail stored).1 =
      (cx.rootsC.toList.map
          (uCost (Prep.ofDag dag) cx.up.w (compAvail cx.up.opaq cx.members avail))).sum +
        (cx.storedInC.toList.map
          (uInl (Prep.ofDag dag) cx.up.w (compAvail cx.up.opaq cx.members avail))).sum +
        (stored.toList.map
          (uInl (Prep.ofDag dag) cx.up.w (compAvail cx.up.opaq cx.members avail))).sum := by
  obtain ⟨hwsz', hwidth, hsz, hrows⟩ := compEval_rows hwf cx.up.w cx.up.opaq cx.members hmem avail
    cx.widthCs hwsz hwcs
  unfold SCtx.phiE
  rw [hprep, hall, hbase, hclo]
  dsimp only
  generalize hW : cx.members.foldl (fun acc t => if avail t = true then
    acc.set! t (some cx.up.w) else acc) cx.widthCs = width at hwsz' hwidth hsz hrows
  have hev : (upClosure dag ((markTable dag.size cx.members)[·]!)).foldl
      (evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
        (Prep.ofDag dag).tail width (Array.replicate dag.size true))
      ((Prep.ofDag dag).eval cx.widthCs (Array.replicate dag.size true)) =
      evalFold dag width (Array.replicate dag.size true)
        (upClosure dag ((markTable dag.size cx.members)[·]!)).toList
        ((Prep.ofDag dag).eval cx.widthCs (Array.replicate dag.size true)) := by
    unfold evalFold; rw [Array.foldl_toList]
  rw [hev]
  generalize evalFold dag width (Array.replicate dag.size true)
    (upClosure dag ((markTable dag.size cx.members)[·]!)).toList
    ((Prep.ofDag dag).eval cx.widthCs (Array.replicate dag.size true)) = ev at hsz hrows
  rw [arr_foldl_add_eq_sum, arr_foldl_add_eq_sum, arr_foldl_add_eq_sum]
  simp only [Nat.zero_add]
  have hroot : ∀ r, ev.cost[r]! = uCost (Prep.ofDag dag) cx.up.w
      (compAvail cx.up.opaq cx.members avail) r := by
    intro r
    by_cases hr : r < dag.size
    · exact (hrows r hr).1
    · rw [uCost_of_ge _ _ _ (by simp only [ofDag_dag]; omega)]
      simp [show ¬ r < ev.cost.size by omega]
  have hent : ∀ x, x < dag.size →
      (evalStep (Prep.ofDag dag).dag (Prep.ofDag dag).family (Prep.ofDag dag).spineLen
        (Prep.ofDag dag).tail (width.set! x none) (Array.replicate dag.size true) ev x).cost[x]! =
      uInl (Prep.ofDag dag) cx.up.w (compAvail cx.up.opaq cx.members avail) x :=
    fun x hx => entry_inl hwf width hwsz' hwidth ev hsz hrows hx
  congr 1
  · congr 1
    · congr 1
      exact List.map_congr_left (fun r _ => hroot r)
    · congr 1
      exact List.map_congr_left (fun x hx => hent x (hsc x (Array.mem_toList_iff.mp hx)))
  · congr 1
    exact List.map_congr_left (fun x hx => hent x (hst x (Array.mem_toList_iff.mp hx)))

end Ix.Compile.Verify.UniformModel
