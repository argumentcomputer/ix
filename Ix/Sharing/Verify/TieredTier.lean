import Ix.Sharing.Verify.TieredSelect

/-!
# Tiered construction, phase 2: the first tier

`firstTier topo weight deps cap` returns a set `F` of stored terms that is
closed under the dependency relation `deps` (here: the terms each phase-1
body references), has at most `cap` terms, and has the maximum total weight
(here: reference count) among all such sets; among the maximum sets it is
the first in the tie order: order the stored terms by weight descending,
then ID ascending (`tierOrder`); at the first term in this order where two
sets differ, the chosen set contains it (`firstTier_spec`).

The search is a depth-first branch and bound. Its correctness is stated
against the unpruned enumeration `tierLeaves`: every closed set is a leaf,
the leaves are in the tie order, and pruning only skips leaves that are no
heavier than the best set found so far.
-/

namespace Ix.Sharing.Verify.Tiered

open Ix.Sharing.Exact

/-! ## Sets, weights and the tie order -/

/-- Total weight of a list of terms. -/
def wsum (weight : Nat → Nat) (G : List Nat) : Nat := (G.map weight).sum

/-- `x` is reachable from `t` along dependencies (reflexively). -/
inductive DReach (deps : Nat → List Nat) : Nat → Nat → Prop
  | refl (t : Nat) : DReach deps t t
  | step {t d x : Nat} : d ∈ deps t → DReach deps d x → DReach deps t x

/-- `G` contains the dependencies of its members. -/
def Closed (deps : Nat → List Nat) (G : List Nat) : Prop :=
  ∀ u ∈ G, ∀ d ∈ deps u, d ∈ G

/-- A first-tier candidate: stored terms without repeats, closed under
dependencies, at most `cap` of them. -/
def Feasible (deps : Nat → List Nat) (items : List Nat) (cap : Nat) (G : List Nat) : Prop :=
  G.Nodup ∧ (∀ x ∈ G, x ∈ items) ∧ Closed deps G ∧ G.length ≤ cap

/-- `A` precedes `B` in the tie order over `items`: at the first item where
they differ, `A` contains it. -/
def PrecIn : List Nat → List Nat → List Nat → Prop
  | [], _, _ => False
  | t :: ts, A, B => (t ∈ A ∧ t ∉ B) ∨ ((t ∈ A ↔ t ∈ B) ∧ PrecIn ts A B)

theorem PrecIn.congr {items A B A' B' : List Nat} (hA : ∀ x, x ∈ A ↔ x ∈ A')
    (hB : ∀ x, x ∈ B ↔ x ∈ B') (h : PrecIn items A B) : PrecIn items A' B' := by
  induction items with
  | nil => exact h
  | cons t ts ih =>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨(hA t).mp h1, fun h => h2 ((hB t).mpr h)⟩
    · exact Or.inr ⟨by rw [← hA, ← hB]; exact h1, ih h2⟩

theorem PrecIn.irrefl {items A : List Nat} : ¬ PrecIn items A A := by
  induction items with
  | nil => exact id
  | cons t ts ih =>
    rintro (⟨h1, h2⟩ | ⟨_, h2⟩)
    · exact h2 h1
    · exact ih h2

theorem PrecIn.append {pre rest A B : List Nat} (hpre : ∀ x ∈ pre, x ∈ A ↔ x ∈ B)
    (h : PrecIn rest A B) : PrecIn (pre ++ rest) A B := by
  induction pre with
  | nil => exact h
  | cons t ts ih =>
    exact Or.inr ⟨hpre t List.mem_cons_self,
      ih fun x hx => hpre x (List.mem_cons_of_mem _ hx)⟩

/-! ## The search bound -/

/-- The sum of the first `k` weights. -/
def topSum (weight : Nat → Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 0
  | a :: l, k + 1 => weight a + topSum weight l k

theorem tierBound_eq (weight : Nat → Nat) (inF : List Nat) :
    ∀ (rest : List Nat) (room acc : Nat),
      tierBound weight inF rest room acc =
        acc + topSum weight (rest.filter fun x => !inF.contains x) room := by
  intro rest
  induction rest with
  | nil => intro room acc; simp [tierBound, topSum]
  | cons t ts ih =>
    intro room acc
    simp only [tierBound]
    by_cases hr : room = 0
    · subst hr
      simp only [ite_true]
      cases h : (t :: ts).filter (fun x => !inF.contains x) <;> simp [topSum]
    · rw [ite_eq_right hr]
      by_cases hc : inF.contains t = true
      · rw [ite_eq_left hc, ih]
        have hc' : t ∈ inF := by simpa using hc
        simp [hc']
      · rw [ite_eq_right hc, ih]
        obtain ⟨r, rfl⟩ : ∃ r, room = r + 1 := ⟨room - 1, by omega⟩
        simp only [List.filter_cons, hc, Bool.not_false, ite_true, topSum,
          Nat.add_sub_cancel]
        omega

theorem topSum_succ_le (weight : Nat → Nat) {m : Nat} :
    ∀ (l : List Nat) (k : Nat), (∀ x ∈ l, weight x ≤ m) →
      topSum weight l (k + 1) ≤ m + topSum weight l k := by
  intro l
  induction l with
  | nil => intro k _; simp [topSum]
  | cons b l ih =>
    intro k hl
    have hb := hl b List.mem_cons_self
    cases k with
    | zero => simp only [topSum]; have := ih 0 (fun x hx => hl x (List.mem_cons_of_mem _ hx)); cases l <;> simp_all [topSum]
    | succ k =>
      simp only [topSum]
      have := ih k (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      omega

theorem wsum_perm {weight : Nat → Nat} {A B : List Nat} (h : A.Perm B) :
    wsum weight A = wsum weight B := (h.map weight).sum_nat

theorem wsum_append (weight : Nat → Nat) (A B : List Nat) :
    wsum weight (A ++ B) = wsum weight A + wsum weight B := by
  simp [wsum]

theorem wsum_cons (weight : Nat → Nat) (a : Nat) (A : List Nat) :
    wsum weight (a :: A) = weight a + wsum weight A := by
  simp [wsum]

/-- Any `k` distinct members of a list in decreasing weight weigh at most its
first `k`. -/
theorem wsum_le_topSum (weight : Nat → Nat) :
    ∀ (L X : List Nat) (k : Nat), L.Pairwise (fun a b => weight b ≤ weight a) → L.Nodup →
      X.Nodup → (∀ x ∈ X, x ∈ L) → X.length ≤ k → wsum weight X ≤ topSum weight L k := by
  intro L
  induction L with
  | nil =>
    intro X k _ _ _ hsub _
    cases X with
    | nil => simp [wsum, topSum]
    | cons x _ => exact absurd (hsub x List.mem_cons_self) (by simp)
  | cons a l ih =>
    intro X k hsort hnd hX hsub hlen
    rw [List.pairwise_cons] at hsort
    rw [List.nodup_cons] at hnd
    cases k with
    | zero =>
      have : X = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      simp [wsum, topSum]
    | succ k =>
      simp only [topSum]
      by_cases ha : a ∈ X
      · have hperm := List.perm_cons_erase ha
        rw [wsum_perm hperm, wsum_cons]
        have hX' : (X.erase a).Nodup := hX.erase a
        have hsub' : ∀ x ∈ X.erase a, x ∈ l := by
          intro x hx
          have hxa : x ≠ a := fun h => by subst h; exact (hX.not_mem_erase) hx
          rcases List.mem_cons.mp (hsub x (List.mem_of_mem_erase hx)) with h | h
          · exact absurd h hxa
          · exact h
        have hlen' : (X.erase a).length ≤ k := by
          rw [List.length_erase_of_mem ha]; omega
        have := ih (X.erase a) k hsort.2 hnd.2 hX' hsub' hlen'
        omega
      · have hsub' : ∀ x ∈ X, x ∈ l := by
          intro x hx
          rcases List.mem_cons.mp (hsub x hx) with h | h
          · exact absurd (h ▸ hx) ha
          · exact h
        have h1 := ih X (k + 1) hsort.2 hnd.2 hX hsub' hlen
        have h2 := topSum_succ_le weight l k hsort.1
        omega

/-! ## Closures -/

/-- `L` lists the terms reachable from `t`, without repeats. -/
def IsClosure (deps : Nat → List Nat) (t : Nat) (L : List Nat) : Prop :=
  L.Nodup ∧ ∀ x, x ∈ L ↔ DReach deps t x

/-- More than `cap` terms are reachable from `t`. -/
def Big (deps : Nat → List Nat) (cap t : Nat) : Prop :=
  ∃ L : List Nat, L.Nodup ∧ (∀ x ∈ L, DReach deps t x) ∧ cap < L.length

/-- A computed closure entry: the closure if it has at most `cap` terms,
`none` if it has more. -/
def ClosureOK (deps : Nat → List Nat) (cap : Nat) : Option (List Nat) → Nat → Prop
  | some L, t => IsClosure deps t L ∧ L.length ≤ cap
  | none, t => Big deps cap t

theorem DReach.trans {deps : Nat → List Nat} {a b c : Nat} (h₁ : DReach deps a b)
    (h₂ : DReach deps b c) : DReach deps a c := by
  induction h₁ with
  | refl => exact h₂
  | step hd _ ih => exact .step hd (ih h₂)

theorem Big.of_dep {deps : Nat → List Nat} {cap t d : Nat} (hd : d ∈ deps t)
    (h : Big deps cap d) : Big deps cap t := by
  obtain ⟨L, hnd, hr, hlen⟩ := h
  exact ⟨L, hnd, fun x hx => .step hd (hr x hx), hlen⟩

theorem Big.not_small {deps : Nat → List Nat} {cap t : Nat} (h : Big deps cap t)
    {L : List Nat} (hL : IsClosure deps t L) : cap < L.length := by
  obtain ⟨B, hnd, hr, hlen⟩ := h
  have := hnd.length_le_of_subset fun x hx => (hL.2 x).mpr (hr x hx)
  omega

theorem foldl_insert_spec :
    ∀ (c a : List Nat), a.Nodup →
      (c.foldl (fun a x => a.insert x) a).Nodup ∧
        ∀ x, x ∈ c.foldl (fun a x => a.insert x) a ↔ x ∈ a ∨ x ∈ c := by
  intro c
  induction c with
  | nil => intro a ha; simp [ha]
  | cons y ys ih =>
    intro a ha
    simp only [List.foldl_cons]
    have hins : (a.insert y).Nodup := by
      by_cases hy : y ∈ a
      · rw [List.insert_of_mem hy]; exact ha
      · rw [List.insert_of_not_mem hy]; exact List.nodup_cons.mpr ⟨hy, ha⟩
    obtain ⟨h1, h2⟩ := ih (a.insert y) hins
    refine ⟨h1, fun x => ?_⟩
    rw [h2, List.mem_insert_iff, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

/-- The running partial closure of `t` after the dependencies `seen`. -/
def AccOK (deps : Nat → List Nat) (cap t : Nat) (seen : List Nat) : Option (List Nat) → Prop
  | some a => a.Nodup ∧ (∀ x ∈ a, DReach deps t x) ∧ t ∈ a ∧
      ∀ d ∈ seen, ∀ x, DReach deps d x → x ∈ a
  | none => Big deps cap t

theorem closureUnion_spec {deps : Nat → List Nat} {cap t : Nat}
    {cl : Std.HashMap Nat (Option (List Nat))}
    (hcl : ∀ d ∈ deps t, ClosureOK deps cap (cl.getD d none) d) :
    ∀ (ds seen : List Nat) (acc : Option (List Nat)), (∀ d ∈ ds, d ∈ deps t) →
      AccOK deps cap t seen acc →
      AccOK deps cap t (seen ++ ds) (ds.foldl (tierClosureUnion cap cl) acc) := by
  intro ds
  induction ds with
  | nil => intro seen acc _ h; simpa using h
  | cons d ds ih =>
    intro seen acc hds hacc
    simp only [List.foldl_cons]
    have hd := hds d List.mem_cons_self
    rw [show seen ++ d :: ds = (seen ++ [d]) ++ ds by simp]
    apply ih _ _ (fun d' h => hds d' (List.mem_cons_of_mem _ h))
    have hok := hcl d hd
    unfold tierClosureUnion
    cases acc with
    | none => exact hacc
    | some a =>
      obtain ⟨hnd, hreach, hta, hseen⟩ := hacc
      cases hc : cl.getD d none with
      | none =>
        rw [hc] at hok
        exact Big.of_dep hd hok
      | some c =>
        rw [hc] at hok
        obtain ⟨⟨hcnd, hcmem⟩, _⟩ := hok
        obtain ⟨hund, humem⟩ := foldl_insert_spec c a hnd
        simp only
        split
        · refine ⟨hund, fun x hx => ?_, (humem t).mpr (Or.inl hta), fun d' hd' x hx => ?_⟩
          · rcases (humem x).mp hx with h | h
            · exact hreach x h
            · exact .step hd ((hcmem x).mp h)
          · rcases List.mem_append.mp hd' with h | h
            · exact (humem x).mpr (Or.inl (hseen d' h x hx))
            · rw [List.mem_singleton] at h
              subst h
              exact (humem x).mpr (Or.inr ((hcmem x).mpr hx))
        · rename_i hlen
          refine ⟨_, hund, fun x hx => ?_, by omega⟩
          rcases (humem x).mp hx with h | h
          · exact hreach x h
          · exact .step hd ((hcmem x).mp h)

/-- The closure entry computed for `t` from its dependencies' entries. -/
theorem closureEntry_spec {deps : Nat → List Nat} {cap t : Nat}
    {cl : Std.HashMap Nat (Option (List Nat))}
    (hcl : ∀ d ∈ deps t, ClosureOK deps cap (cl.getD d none) d) :
    ClosureOK deps cap (((deps t).foldl (tierClosureUnion cap cl) (some [t])).bind
      fun a => if a.length ≤ cap then some a else none) t := by
  have hinit : AccOK deps cap t [] (some [t]) :=
    ⟨(by simp : [t].Nodup), fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact .refl _,
      List.mem_singleton_self t, fun _ h => absurd h (by simp)⟩
  have h := closureUnion_spec hcl (deps t) [] (some [t]) (fun _ h => h) hinit
  simp only [List.nil_append] at h
  generalize (deps t).foldl (tierClosureUnion cap cl) (some [t]) = acc at h
  cases acc with
  | none => exact h
  | some a =>
    obtain ⟨hnd, hreach, hta, hall⟩ := h
    simp only [Option.bind_some]
    split
    · rename_i hlen
      refine ⟨⟨hnd, fun x => ⟨hreach x, fun hx => ?_⟩⟩, hlen⟩
      cases hx with
      | refl => exact hta
      | step hd hr => exact hall _ hd x hr
    · rename_i hlen
      exact ⟨a, hnd, hreach, by omega⟩

/-- The closures computed so far, for the terms `done`. -/
def CInv (deps : Nat → List Nat) (cap : Nat) (cl : Std.HashMap Nat (Option (List Nat)))
    (done : List Nat) : Prop :=
  (∀ x, cl.contains x = true ↔ x ∈ done) ∧ done.Nodup ∧
    (∀ x ∈ done, ClosureOK deps cap (cl.getD x none) x) ∧ ∀ x ∈ done, ∀ d ∈ deps x, d ∈ done

theorem checkInternal_ok {b : Bool} {msg : String} {u : Unit}
    (h : checkInternal b msg = .ok u) : b = true := by
  unfold checkInternal at h
  split at h
  · assumption
  · cases h

theorem tierClosures_fold {deps : Nat → List Nat} {cap : Nat} :
    ∀ (l done : List Nat) (cl cl' : Std.HashMap Nat (Option (List Nat))),
      CInv deps cap cl done →
      l.foldlM (fun cl t => do
          checkInternal (!cl.contains t) "a stored term repeats in the phase-1 table"
          checkInternal ((deps t).all cl.contains) "a phase-1 body references a later entry"
          let acc := (deps t).foldl (tierClosureUnion cap cl) (some [t])
          return cl.insert t (acc.bind fun a => if a.length ≤ cap then some a else none))
        cl = .ok cl' →
      CInv deps cap cl' (done ++ l) := by
  intro l
  induction l with
  | nil =>
    intro done cl cl' hinv h
    simp only [List.foldlM_nil] at h
    cases h
    simpa using hinv
  | cons t ts ih =>
    intro done cl cl' hinv h
    simp only [List.foldlM_cons] at h
    obtain ⟨cl1, h1, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
    obtain ⟨_, hc1, h1⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h1
    obtain ⟨_, hc2, h1⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h1
    have hnew := checkInternal_ok hc1
    have hdeps := checkInternal_ok hc2
    simp only [pure, Except.pure, Except.ok.injEq] at h1
    subst h1
    rw [show done ++ t :: ts = (done ++ [t]) ++ ts by simp]
    apply ih _ _ _ _ h
    obtain ⟨hcont, hnd, hok, hclosed⟩ := hinv
    have htd : t ∉ done := by
      intro ht
      rw [← hcont] at ht
      simp [ht] at hnew
    have hdd : ∀ d ∈ deps t, d ∈ done := by
      intro d hd
      rw [List.all_eq_true] at hdeps
      exact (hcont d).mp (hdeps d hd)
    have hdok : ∀ d ∈ deps t, ClosureOK deps cap (cl.getD d none) d :=
      fun d hd => hok d (hdd d hd)
    refine ⟨fun x => ?_, ?_, fun x hx => ?_, fun x hx d hd => ?_⟩
    · rw [Std.HashMap.contains_insert, Bool.or_eq_true, hcont, List.mem_append,
        List.mem_singleton, beq_iff_eq]
      constructor
      · rintro (h | h)
        · exact Or.inr h.symm
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h.symm
    · exact List.nodup_append.mpr ⟨hnd, (by simp : [t].Nodup),
        fun a ha b hb => by rw [List.mem_singleton] at hb; subst hb; exact fun h => htd (h ▸ ha)⟩
    · rw [Std.HashMap.getD_insert]
      rcases List.mem_append.mp hx with hx | hx
      · have : (t == x) = false := by
          rw [beq_eq_false_iff_ne]; exact fun h => htd (h ▸ hx)
        rw [this]
        exact hok x hx
      · rw [List.mem_singleton] at hx
        subst hx
        simp only [beq_self_eq_true, ite_true]
        exact closureEntry_spec hdok
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (hclosed x hx d hd)
      · rw [List.mem_singleton] at hx
        subst hx
        exact List.mem_append_left _ (hdd d hd)

/-- **Closures.** A successful `tierClosures` saw every term once, every
dependency before its user, and computed the closure of every term (or
`none` when it has more than `cap` terms). -/
theorem tierClosures_spec {topo : Array Nat} {deps : Nat → List Nat} {cap : Nat}
    {cl : Std.HashMap Nat (Option (List Nat))} (h : tierClosures topo deps cap = .ok cl) :
    topo.toList.Nodup ∧ (∀ t ∈ topo.toList, ClosureOK deps cap (cl.getD t none) t) ∧
      ∀ t ∈ topo.toList, ∀ d ∈ deps t, d ∈ topo.toList := by
  unfold tierClosures at h
  rw [← Array.foldlM_toList] at h
  have hinit : CInv deps cap {} [] :=
    ⟨fun x => by simp, List.nodup_nil, fun _ h => absurd h (by simp), fun _ h => absurd h (by simp)⟩
  obtain ⟨_, hnd, hok, hclosed⟩ := tierClosures_fold _ [] {} cl hinit h
  simp only [List.nil_append] at hnd hok hclosed
  exact ⟨hnd, hok, hclosed⟩

/-! ## The unpruned search -/

/-- The leaves of the search below a node, in search order, without pruning:
`rest` are the undecided items, `inF` the chosen set and `ex` the excluded
terms. -/
def tierLeaves (closure : Nat → Option (List Nat)) (cap : Nat) :
    List Nat → List Nat → List Nat → List (List Nat)
  | [], inF, _ => [inF]
  | t :: ts, inF, ex =>
    if inF.contains t then tierLeaves closure cap ts inF ex
    else
      (match closure t with
        | some c =>
          if !c.any ex.contains && inF.length + (c.filter (!inF.contains ·)).length ≤ cap then
            tierLeaves closure cap ts (inF ++ c.filter (!inF.contains ·)) ex
          else []
        | none => []) ++ tierLeaves closure cap ts inF (t :: ex)

/-- The global facts of a search: distinct items, a correct closure for every
item, and dependencies among the items. -/
structure Ctx (deps : Nat → List Nat) (closure : Nat → Option (List Nat)) (cap : Nat)
    (items : List Nat) : Prop where
  nodup : items.Nodup
  closure : ∀ t ∈ items, ClosureOK deps cap (closure t) t
  deps : ∀ t ∈ items, ∀ d ∈ deps t, d ∈ items

/-- The local facts of a search node: the decided items `pre` are chosen or
excluded, the chosen set is a closed set of items without repeats. -/
def Inv (deps : Nat → List Nat) (items : List Nat) (cap : Nat) (pre inF ex : List Nat) : Prop :=
  inF.Nodup ∧ inF.length ≤ cap ∧ (∀ x ∈ pre, x ∈ inF ∨ x ∈ ex) ∧ (∀ x ∈ ex, x ∉ inF) ∧
    (∀ x ∈ inF, x ∈ items) ∧ Closed deps inF

theorem Ctx.reach {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : List Nat} (hc : Ctx deps closure cap items) {t x : Nat} (ht : t ∈ items)
    (h : DReach deps t x) : x ∈ items := by
  induction h with
  | refl => exact ht
  | step hd _ ih => exact ih (hc.deps _ ht _ hd)

theorem contains_iff {l : List Nat} {x : Nat} : l.contains x = true ↔ x ∈ l := by simp

theorem mem_split {pre rest : List Nat} {x : Nat} (h : x ∈ pre ++ rest) (hx : x ∉ pre) :
    x ∈ rest := by
  rcases List.mem_append.mp h with h | h
  · exact absurd h hx
  · exact h

/-- The include step: the closure of `t` joins the chosen set. -/
theorem Inv.include {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : List Nat} (hctx : Ctx deps closure cap items) {pre inF ex : List Nat} {t : Nat}
    {ts c : List Nat} (hinv : Inv deps items cap pre inF ex) (hitems : items = pre ++ t :: ts)
    (ht : t ∉ inF) (hc : closure t = some c) (hex : c.any ex.contains = false)
    (hlen : inF.length + (c.filter (!inF.contains ·)).length ≤ cap) :
    Inv deps items cap (pre ++ [t]) (inF ++ c.filter (!inF.contains ·)) ex ∧
      (c.filter (!inF.contains ·)).Nodup ∧ t ∈ c.filter (!inF.contains ·) ∧
      ∀ x ∈ c.filter (!inF.contains ·), x ∈ t :: ts ∧ x ∉ inF := by
  obtain ⟨hnd, _, hpre, hexF, hitm, hcl⟩ := hinv
  have htI : t ∈ items := by rw [hitems]; simp
  have hok := hctx.closure t htI
  rw [hc] at hok
  obtain ⟨⟨hcnd, hcmem⟩, _⟩ := hok
  have hcex : ∀ x ∈ c, x ∉ ex := by
    intro x hx hxe
    have : c.any ex.contains = true := List.any_eq_true.mpr ⟨x, hx, contains_iff.mpr hxe⟩
    rw [hex] at this
    cases this
  have hcI : ∀ x ∈ c, x ∈ items := fun x hx => hctx.reach htI ((hcmem x).mp hx)
  have hmemN : ∀ x, x ∈ c.filter (!inF.contains ·) ↔ x ∈ c ∧ x ∉ inF := by
    intro x
    simp
  have hnew : ∀ x ∈ c.filter (!inF.contains ·), x ∈ t :: ts ∧ x ∉ inF := by
    intro x hx
    obtain ⟨hxc, hxi⟩ := (hmemN x).mp hx
    refine ⟨mem_split (hitems ▸ hcI x hxc) fun hxp => ?_, hxi⟩
    rcases hpre x hxp with h | h
    · exact hxi h
    · exact hcex x hxc h
  have htc : t ∈ c := (hcmem t).mpr (.refl t)
  have htN : t ∈ c.filter (!inF.contains ·) := (hmemN t).mpr ⟨htc, ht⟩
  have hNnd : (c.filter (!inF.contains ·)).Nodup := hcnd.filter _
  refine ⟨⟨?_, by simp only [List.length_append]; omega, fun x hx => ?_, fun x hx hxi => ?_,
    fun x hx => ?_, fun u hu d hd => ?_⟩, hNnd, htN, hnew⟩
  · exact List.nodup_append.mpr ⟨hnd, hNnd, fun a ha b hb hab => ((hmemN b).mp hb).2 (hab ▸ ha)⟩
  · rcases List.mem_append.mp hx with hx | hx
    · rcases hpre x hx with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr h
    · rw [List.mem_singleton] at hx
      subst hx
      exact Or.inl (List.mem_append_right _ htN)
  · rcases List.mem_append.mp hxi with h | h
    · exact hexF x hx h
    · exact hcex x ((hmemN x).mp h).1 hx
  · rcases List.mem_append.mp hx with h | h
    · exact hitm x h
    · exact hcI x ((hmemN x).mp h).1
  · rcases List.mem_append.mp hu with h | h
    · exact List.mem_append_left _ (hcl u h d hd)
    · have hdc : d ∈ c := (hcmem d).mpr
        (((hcmem u).mp ((hmemN u).mp h).1).trans (.step hd (.refl d)))
      by_cases hdi : d ∈ inF
      · exact List.mem_append_left _ hdi
      · exact List.mem_append_right _ ((hmemN d).mpr ⟨hdc, hdi⟩)

theorem Inv.exclude {deps : Nat → List Nat} {items : List Nat} {cap : Nat}
    {pre inF ex : List Nat} {t : Nat} (hinv : Inv deps items cap pre inF ex) (ht : t ∉ inF) :
    Inv deps items cap (pre ++ [t]) inF (t :: ex) := by
  obtain ⟨hnd, hlen, hpre, hexF, hitm, hcl⟩ := hinv
  refine ⟨hnd, hlen, fun x hx => ?_, fun x hx => ?_, hitm, hcl⟩
  · rcases List.mem_append.mp hx with hx | hx
    · rcases hpre x hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rw [List.mem_singleton] at hx
      exact Or.inr (hx ▸ List.mem_cons_self)
  · rcases List.mem_cons.mp hx with h | h
    · exact h ▸ ht
    · exact hexF x h

theorem Inv.skip {deps : Nat → List Nat} {items : List Nat} {cap : Nat}
    {pre inF ex : List Nat} {t : Nat} (hinv : Inv deps items cap pre inF ex) (ht : t ∈ inF) :
    Inv deps items cap (pre ++ [t]) inF ex := by
  obtain ⟨hnd, hlen, hpre, hexF, hitm, hcl⟩ := hinv
  refine ⟨hnd, hlen, fun x hx => ?_, hexF, hitm, hcl⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact hpre x hx
  · rw [List.mem_singleton] at hx
    exact Or.inl (hx ▸ ht)

/-- The facts of a leaf: a closed set of at most `cap` items without repeats
avoiding the excluded terms. -/
def LeafOK (deps : Nat → List Nat) (items : List Nat) (cap : Nat) (F ex : List Nat) : Prop :=
  F.Nodup ∧ F.length ≤ cap ∧ (∀ x ∈ ex, x ∉ F) ∧ (∀ x ∈ F, x ∈ items) ∧ Closed deps F

/-- **Leaves.** Every leaf extends the chosen set by distinct undecided items
to a closed set of at most `cap` items avoiding the excluded terms. -/
theorem leaves_shape {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : List Nat} (hctx : Ctx deps closure cap items) :
    ∀ (rest pre inF ex : List Nat), items = pre ++ rest → Inv deps items cap pre inF ex →
      ∀ F ∈ tierLeaves closure cap rest inF ex,
        ∃ X, F = inF ++ X ∧ X.Nodup ∧ (∀ x ∈ X, x ∈ rest ∧ x ∉ inF) ∧
          LeafOK deps items cap F ex := by
  intro rest
  induction rest with
  | nil =>
    intro pre inF ex hitems hinv F hF
    simp only [tierLeaves, List.mem_singleton] at hF
    subst hF
    simp only [List.append_nil] at hitems
    subst hitems
    obtain ⟨h1, h2, _, h4, h5, h6⟩ := hinv
    exact ⟨[], by simp, List.nodup_nil, by simp, h1, h2, h4, h5, h6⟩
  | cons t ts ih =>
    intro pre inF ex hitems hinv F hF
    have hitems' : items = (pre ++ [t]) ++ ts := by rw [hitems]; simp
    simp only [tierLeaves] at hF
    by_cases ht : inF.contains t = true
    · rw [ite_eq_left ht] at hF
      obtain ⟨X, rfl, hX, hXr, hfin⟩ := ih _ _ _ hitems' (hinv.skip (contains_iff.mp ht)) F hF
      exact ⟨X, rfl, hX, fun x hx => ⟨List.mem_cons_of_mem _ (hXr x hx).1, (hXr x hx).2⟩, hfin⟩
    · have ht' : t ∉ inF := fun h => ht (contains_iff.mpr h)
      rw [ite_eq_right ht] at hF
      rcases List.mem_append.mp hF with hI | hE
      · cases hc : closure t with
        | none => rw [hc] at hI; cases hI
        | some c =>
          rw [hc] at hI
          simp only at hI
          split at hI
          · rename_i hcond
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
            obtain ⟨hinv', hNnd, _, hnew⟩ :=
              hinv.include hctx hitems ht' hc hcond.1 hcond.2
            obtain ⟨X, rfl, hX, hXr, hfin⟩ := ih _ _ _ hitems' hinv' F hI
            refine ⟨c.filter (!inF.contains ·) ++ X, by simp, ?_, fun x hx => ?_, hfin⟩
            · refine List.nodup_append.mpr ⟨hNnd, hX, fun a ha b hb hab => ?_⟩
              exact (hXr b hb).2 (List.mem_append_right _ (hab ▸ ha))
            · rcases List.mem_append.mp hx with h | h
              · exact hnew x h
              · exact ⟨List.mem_cons_of_mem _ (hXr x h).1,
                  fun hi => (hXr x h).2 (List.mem_append_left _ hi)⟩
          · cases hI
      · obtain ⟨X, rfl, hX, hXr, ⟨h1, h2, h3, h4, h5⟩⟩ :=
          ih _ _ _ hitems' (hinv.exclude ht') F hE
        refine ⟨X, rfl, hX, fun x hx => ⟨List.mem_cons_of_mem _ (hXr x hx).1, (hXr x hx).2⟩,
          ⟨h1, h2, fun x hx => h3 x (List.mem_cons_of_mem _ hx), h4, h5⟩⟩

/-- **Bound.** Every leaf weighs at most the search bound of its node. -/
theorem leaves_bound {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : List Nat} (hctx : Ctx deps closure cap items) (weight : Nat → Nat)
    (hsort : items.Pairwise fun a b => weight b ≤ weight a)
    {rest pre inF ex : List Nat} (hitems : items = pre ++ rest)
    (hinv : Inv deps items cap pre inF ex) :
    ∀ F ∈ tierLeaves closure cap rest inF ex,
      wsum weight F ≤ tierBound weight inF rest (cap - inF.length) (wsum weight inF) := by
  intro F hF
  obtain ⟨X, rfl, hX, hXr, hleaf⟩ := leaves_shape hctx rest pre inF ex hitems hinv F hF
  rw [tierBound_eq, wsum_append]
  have hrest : rest.Pairwise (fun a b => weight b ≤ weight a) ∧ rest.Nodup := by
    have h1 := hctx.nodup
    rw [hitems] at hsort h1
    exact ⟨(List.pairwise_append.mp hsort).2.1, (List.nodup_append.mp h1).2.1⟩
  have hlen : X.length ≤ cap - inF.length := by
    have := hleaf.2.1
    simp only [List.length_append] at this
    omega
  have := wsum_le_topSum weight (rest.filter fun x => !inF.contains x) X (cap - inF.length)
    (hrest.1.filter _) (hrest.2.filter _) hX
    (fun x hx => List.mem_filter.mpr ⟨(hXr x hx).1, by simpa using (hXr x hx).2⟩) hlen
  omega

/-- A closed set contains everything reachable from its members. -/
theorem Closed.reach {deps : Nat → List Nat} {G : List Nat} (hG : Closed deps G) {t x : Nat}
    (ht : t ∈ G) (h : DReach deps t x) : x ∈ G := by
  induction h with
  | refl => exact ht
  | step hd _ ih => exact ih (hG _ ht _ hd)

/-- **Completeness.** Every feasible set compatible with a node's decisions
is (up to order) a leaf below it. -/
theorem leaves_complete {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : List Nat} (hctx : Ctx deps closure cap items) {G : List Nat}
    (hG : Feasible deps items cap G) :
    ∀ (rest pre inF ex : List Nat), items = pre ++ rest → Inv deps items cap pre inF ex →
      (∀ x ∈ inF, x ∈ G) → (∀ x ∈ ex, x ∉ G) → (∀ x ∈ pre, x ∈ G → x ∈ inF) →
      ∃ F ∈ tierLeaves closure cap rest inF ex, ∀ x, x ∈ F ↔ x ∈ G := by
  obtain ⟨hGnd, hGitems, hGcl, hGlen⟩ := hG
  intro rest
  induction rest with
  | nil =>
    intro pre inF ex hitems _ hin _ hpre
    simp only [List.append_nil] at hitems
    subst hitems
    exact ⟨inF, by simp [tierLeaves], fun x => ⟨hin x, fun hx => hpre x (hGitems x hx) hx⟩⟩
  | cons t ts ih =>
    intro pre inF ex hitems hinv hin hex hpre
    have hitems' : items = (pre ++ [t]) ++ ts := by rw [hitems]; simp
    simp only [tierLeaves]
    by_cases ht : inF.contains t = true
    · rw [ite_eq_left ht]
      have ht' := contains_iff.mp ht
      refine ih _ _ _ hitems' (hinv.skip ht') hin hex fun x hx hxG => ?_
      rcases List.mem_append.mp hx with h | h
      · exact hpre x h hxG
      · rw [List.mem_singleton] at h; exact h ▸ ht'
    · have ht' : t ∉ inF := fun h => ht (contains_iff.mpr h)
      rw [ite_eq_right ht]
      have htI : t ∈ items := by rw [hitems]; simp
      by_cases htG : t ∈ G
      · -- include
        have hok := hctx.closure t htI
        cases hc : closure t with
        | none =>
          rw [hc] at hok
          obtain ⟨L, hLnd, hLr, hLlen⟩ := hok
          have := hLnd.length_le_of_subset fun x hx => hGcl.reach htG (hLr x hx)
          omega
        | some c =>
          rw [hc] at hok
          obtain ⟨⟨hcnd, hcmem⟩, _⟩ := hok
          have hcG : ∀ x ∈ c, x ∈ G := fun x hx => hGcl.reach htG ((hcmem x).mp hx)
          have hex' : c.any ex.contains = false := by
            rw [Bool.eq_false_iff]
            intro h
            obtain ⟨x, hx, hxe⟩ := List.any_eq_true.mp h
            exact hex x (contains_iff.mp hxe) (hcG x hx)
          have hlen : inF.length + (c.filter (!inF.contains ·)).length ≤ cap := by
            have hnd : (inF ++ c.filter (!inF.contains ·)).Nodup :=
              List.nodup_append.mpr ⟨hinv.1, hcnd.filter _, fun a ha b hb hab => by
                have hb' := (List.mem_filter.mp hb).2
                simp only [Bool.not_eq_true'] at hb'
                exact (by simpa using hb' : b ∉ inF) (hab ▸ ha)⟩
            have := hnd.length_le_of_subset fun x hx => by
              rcases List.mem_append.mp hx with h | h
              · exact hin x h
              · exact hcG x (List.mem_filter.mp h).1
            simp only [List.length_append] at this
            omega
          obtain ⟨hinv', _, htN, _⟩ := hinv.include hctx hitems ht' hc hex' hlen
          have hcond : (!c.any ex.contains && decide (inF.length +
              (c.filter (!inF.contains ·)).length ≤ cap)) = true := by
            rw [hex']; simpa using hlen
          obtain ⟨F, hF, hFG⟩ := ih _ _ _ hitems' hinv'
            (fun x hx => by
              rcases List.mem_append.mp hx with h | h
              · exact hin x h
              · exact hcG x (List.mem_filter.mp h).1)
            hex (fun x hx hxG => by
              rcases List.mem_append.mp hx with h | h
              · exact List.mem_append_left _ (hpre x h hxG)
              · rw [List.mem_singleton] at h; subst h
                exact List.mem_append_right _ htN)
          refine ⟨F, List.mem_append_left _ ?_, hFG⟩
          dsimp only
          rw [ite_eq_left hcond]
          exact hF
      · -- exclude
        obtain ⟨F, hF, hFG⟩ := ih _ _ _ hitems' (hinv.exclude ht') hin
          (fun x hx => by
            rcases List.mem_cons.mp hx with h | h
            · exact h ▸ htG
            · exact hex x h)
          (fun x hx hxG => by
            rcases List.mem_append.mp hx with h | h
            · exact hpre x h hxG
            · rw [List.mem_singleton] at h; exact absurd (h ▸ hxG) htG)
        exact ⟨F, List.mem_append_right _ hF, hFG⟩

/-- **Order.** The leaves come in the tie order. -/
theorem leaves_order {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : List Nat} (hctx : Ctx deps closure cap items) :
    ∀ (rest pre inF ex : List Nat), items = pre ++ rest → Inv deps items cap pre inF ex →
      (tierLeaves closure cap rest inF ex).Pairwise (PrecIn rest) := by
  intro rest
  induction rest with
  | nil => intro _ inF _ _ _; simp [tierLeaves]
  | cons t ts ih =>
    intro pre inF ex hitems hinv
    have hitems' : items = (pre ++ [t]) ++ ts := by rw [hitems]; simp
    simp only [tierLeaves]
    by_cases ht : inF.contains t = true
    · rw [ite_eq_left ht]
      have ht' := contains_iff.mp ht
      have hsub := ih _ _ _ hitems' (hinv.skip ht')
      refine hsub.imp_of_mem fun {A B} hA hB hAB => Or.inr ⟨?_, hAB⟩
      obtain ⟨X, rfl, -⟩ := leaves_shape hctx ts _ _ _ hitems' (hinv.skip ht') A hA
      obtain ⟨Y, rfl, -⟩ := leaves_shape hctx ts _ _ _ hitems' (hinv.skip ht') B hB
      exact iff_of_true (List.mem_append_left _ ht') (List.mem_append_left _ ht')
    · have ht' : t ∉ inF := fun h => ht (contains_iff.mpr h)
      rw [ite_eq_right ht]
      have hE := ih _ _ _ hitems' (hinv.exclude ht')
      have hEt : ∀ B ∈ tierLeaves closure cap ts inF (t :: ex), t ∉ B := by
        intro B hB
        obtain ⟨_, _, _, _, ⟨_, _, hav, _⟩⟩ :=
          leaves_shape hctx ts _ _ _ hitems' (hinv.exclude ht') B hB
        exact hav t List.mem_cons_self
      -- the include part
      have hI : ∀ (I : List (List Nat)), (I = match closure t with
          | some c =>
            if (!c.any ex.contains && decide (inF.length +
                (c.filter (!inF.contains ·)).length ≤ cap)) = true then
              tierLeaves closure cap ts (inF ++ c.filter (!inF.contains ·)) ex
            else []
          | none => []) →
          I.Pairwise (PrecIn (t :: ts)) ∧ ∀ A ∈ I, t ∈ A := by
        intro I hIdef
        cases hc : closure t with
        | none => rw [hc] at hIdef; subst hIdef; simp
        | some c =>
          rw [hc] at hIdef
          dsimp only at hIdef
          split at hIdef
          · rename_i hcond
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
            obtain ⟨hinv', _, htN, _⟩ := hinv.include hctx hitems ht' hc hcond.1 hcond.2
            subst hIdef
            have hin : ∀ A ∈ tierLeaves closure cap ts (inF ++ c.filter (!inF.contains ·)) ex,
                t ∈ A := by
              intro A hA
              obtain ⟨X, rfl, -⟩ := leaves_shape hctx ts _ _ _ hitems' hinv' A hA
              exact List.mem_append_left _ (List.mem_append_right _ htN)
            refine ⟨(ih _ _ _ hitems' hinv').imp_of_mem fun {A B} hA hB hAB =>
              Or.inr ⟨iff_of_true (hin A hA) (hin B hB), hAB⟩, hin⟩
          · subst hIdef; simp
      obtain ⟨hIp, hIt⟩ := hI _ rfl
      refine List.pairwise_append.mpr ⟨hIp, hE.imp_of_mem fun {A B} hA hB hAB =>
        Or.inr ⟨iff_of_false (hEt A hA) (hEt B hB), hAB⟩, fun A hA B hB => ?_⟩
      exact Or.inl ⟨hIt A hA, hEt B hB⟩

theorem leaves_ne_nil (closure : Nat → Option (List Nat)) (cap : Nat) :
    ∀ (rest inF ex : List Nat), tierLeaves closure cap rest inF ex ≠ [] := by
  intro rest
  induction rest with
  | nil => intro _ _; simp [tierLeaves]
  | cons t ts ih =>
    intro inF ex
    simp only [tierLeaves]
    split
    · exact ih _ _
    · intro h
      exact ih inF (t :: ex) (List.append_eq_nil_iff.mp h).2

/-! ## The best leaf -/

/-- The search's update at a leaf. -/
def leafUpd (weight : Nat → Nat) (best : Option (Nat × List Nat)) (F : List Nat) :
    Option (Nat × List Nat) :=
  tierUpd best (wsum weight F) F

theorem fold_noop (weight : Nat → Nat) {b : Nat} {B : List Nat} :
    ∀ (L : List (List Nat)), (∀ F ∈ L, wsum weight F ≤ b) →
      L.foldl (leafUpd weight) (some (b, B)) = some (b, B) := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons F L ih =>
    intro h
    simp only [List.foldl_cons, leafUpd, tierUpd]
    rw [ite_eq_right (by have := h F List.mem_cons_self; omega)]
    exact ih fun G hG => h G (List.mem_cons_of_mem _ hG)

/-- The fold over the leaves keeps the first heaviest leaf. -/
theorem fold_best (weight : Nat → Nat) (items : List Nat) :
    ∀ (L : List (List Nat)) (init : Option (Nat × List Nat)), L.Pairwise (PrecIn items) →
      (∀ b R, init = some (b, R) → b = wsum weight R ∧ ∀ G ∈ L, PrecIn items R G) →
      ((init ≠ none ∨ L ≠ []) → L.foldl (leafUpd weight) init ≠ none) ∧
      ∀ b R, L.foldl (leafUpd weight) init = some (b, R) →
        b = wsum weight R ∧ (R ∈ L ∨ init = some (b, R)) ∧ (∀ G ∈ L, wsum weight G ≤ b) ∧
        (∀ b0 R0, init = some (b0, R0) → b0 ≤ b ∧ (b0 = b → R0 = R)) ∧
        (∀ G ∈ L, wsum weight G = b → G = R ∨ PrecIn items R G) := by
  intro L
  induction L with
  | nil =>
    intro init _ hinit
    refine ⟨fun h => by simpa using h, fun b R h => ?_⟩
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨(hinit b R rfl).1, Or.inr rfl, by simp, fun b0 R0 h => by
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨by omega, fun _ => h.2.symm⟩, by simp⟩
  | cons F L ih =>
    intro init hpw hinit
    rw [List.pairwise_cons] at hpw
    simp only [List.foldl_cons]
    -- the state after `F`
    have hstep : ∀ b' R', leafUpd weight init F = some (b', R') →
        b' = wsum weight R' ∧ (∀ G ∈ L, PrecIn items R' G) ∧ wsum weight F ≤ b' ∧
        ((R' = F ∧ b' = wsum weight F) ∨ init = some (b', R')) ∧
        (∀ b0 R0, init = some (b0, R0) → b0 ≤ b' ∧ (b0 = b' → R0 = R')) ∧
        (wsum weight F = b' → F = R' ∨ PrecIn items R' F) := by
      intro b' R' h
      unfold leafUpd tierUpd at h
      cases init with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hpw.1, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩, (fun _ _ h => nomatch h),
          fun _ => Or.inl rfl⟩
      | some bR =>
        obtain ⟨b0, R0⟩ := bR
        obtain ⟨hb0, hR0⟩ := hinit b0 R0 rfl
        simp only at h
        split at h
        · rename_i hgt
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, hpw.1, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩,
            fun b1 R1 h1 => by
              simp only [Option.some.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              exact ⟨by omega, fun h => by omega⟩,
            fun _ => Or.inl rfl⟩
        · rename_i hle
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hb0, fun G hG => hR0 G (List.mem_cons_of_mem _ hG), by omega, Or.inr rfl,
            fun b1 R1 h1 => by
              simp only [Option.some.injEq, Prod.mk.injEq] at h1
              obtain ⟨rfl, rfl⟩ := h1
              exact ⟨Nat.le_refl _, fun _ => rfl⟩,
            fun _ => Or.inr (hR0 F List.mem_cons_self)⟩
    have hsome : leafUpd weight init F ≠ none := by
      unfold leafUpd tierUpd
      cases init with
      | none => simp
      | some bR => obtain ⟨b0, R0⟩ := bR; simp only; split <;> simp
    obtain ⟨hne, hres⟩ := ih (leafUpd weight init F) hpw.2 (fun b' R' h =>
      ⟨(hstep b' R' h).1, (hstep b' R' h).2.1⟩)
    refine ⟨fun _ => hne (Or.inl hsome), fun b R h => ?_⟩
    obtain ⟨b', R', hbR'⟩ : ∃ b' R', leafUpd weight init F = some (b', R') := by
      cases h' : leafUpd weight init F with
      | none => exact absurd h' hsome
      | some p => exact ⟨p.1, p.2, rfl⟩
    obtain ⟨hbw, hmem, hle, hmono, htie⟩ := hres b R h
    obtain ⟨_, _, hFle, hsrc, hmono', htieF⟩ := hstep b' R' hbR'
    obtain ⟨hb'b, hb'R⟩ := hmono b' R' hbR'
    refine ⟨hbw, ?_, ?_, ?_, ?_⟩
    · rcases hmem with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · rw [hbR'] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rcases hsrc with ⟨rfl, _⟩ | h2
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h2
    · intro G hG
      rcases List.mem_cons.mp hG with rfl | hG
      · omega
      · exact hle G hG
    · intro b0 R0 h0
      obtain ⟨h1, h2⟩ := hmono' b0 R0 h0
      exact ⟨by omega, fun h => by rw [h2 (by omega)]; exact hb'R (by omega)⟩
    · intro G hG hGb
      rcases List.mem_cons.mp hG with rfl | hG
      · have : wsum weight G = b' := by omega
        rw [← hb'R (by omega)]
        exact htieF this
      · exact htie G hG hGb

/-! ## The pruned search -/

theorem foldl_weight (weight : Nat → Nat) :
    ∀ (l : List Nat) (cur : Nat), l.foldl (fun acc u => acc + weight u) cur = cur + wsum weight l := by
  intro l
  induction l with
  | nil => intro cur; simp [wsum]
  | cons a l ih => intro cur; simp only [List.foldl_cons, ih, wsum_cons]; omega

/-- **Search.** A successful run from a node folds the best-set update over
the node's leaves in search order: pruning skips only leaves no heavier
than the best set. -/
theorem tierDfs_spec {deps : Nat → List Nat} {closure : Nat → Option (List Nat)} {cap : Nat}
    {items : Array Nat} (hctx : Ctx deps closure cap items.toList) (weight : Nat → Nat)
    (hsort : items.toList.Pairwise fun a b => weight b ≤ weight a) (limits : Limits) :
    ∀ (fuel pos cur : Nat) (inF : List Nat) (excluded : Std.HashSet Nat) (ex : List Nat)
      (st st' : TierState),
      cur = wsum weight inF → (∀ u, excluded.contains u = true ↔ u ∈ ex) →
      Inv deps items.toList cap (items.toList.take pos) inF ex →
      tierDfs items weight closure cap limits fuel pos cur inF excluded st = .ok st' →
      st'.best = (tierLeaves closure cap (items.toList.drop pos) inF ex).foldl
        (leafUpd weight) st.best := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ h; unfold tierDfs at h; cases h
  | succ fuel ih =>
    intro pos cur inF excluded ex st st' hcur hex hinv h
    have hsplit := (List.take_append_drop pos items.toList).symm
    rw [tierDfs] at h
    split at h
    · cases h
    · dsimp only at h
      split at h
      · -- pruned
        rename_i hpr
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only
        unfold tierPruned at hpr
        split at hpr
        · rename_i b B hbB
          rw [hbB]
          refine (fold_noop weight _ fun F hF => ?_).symm
          have := leaves_bound hctx weight hsort hsplit hinv F hF
          rw [← hcur] at this
          simp only [decide_eq_true_eq] at hpr
          omega
        · cases hpr
      · split at h
        · -- a leaf
          rename_i _ hpos
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          rw [List.drop_eq_nil_of_le (by simpa using hpos)]
          simp [tierLeaves, leafUpd, hcur]
        · rename_i _ hpos
          have hlt : pos < items.toList.length := by simp; omega
          have hdrop : items.toList.drop pos = items[pos]! :: items.toList.drop (pos + 1) := by
            rw [List.drop_eq_getElem_cons hlt]
            simp [getElem!_pos items pos (by simpa using hlt)]
          have htake : items.toList.take (pos + 1) = items.toList.take pos ++ [items[pos]!] := by
            rw [List.take_succ_eq_append_getElem hlt]
            simp [getElem!_pos items pos (by simpa using hlt)]
          have hitems : items.toList = items.toList.take pos ++ items[pos]! ::
              items.toList.drop (pos + 1) := by rw [← hdrop]; exact hsplit
          rw [hdrop]
          simp only [tierLeaves]
          generalize hst1 : ({ st with states := st.states + 1 } : TierState) = st1 at h
          have hb1 : st1.best = st.best := by rw [← hst1]
          split at h
          · rename_i hin
            rw [ite_eq_left hin, ← hb1]
            refine ih _ _ _ _ _ _ _ hcur hex ?_ h
            rw [htake]
            exact hinv.skip (contains_iff.mp hin)
          · rename_i hin
            rw [ite_eq_right hin, List.foldl_append]
            have ht' : items[pos]! ∉ inF := fun h => hin (contains_iff.mpr h)
            have hex' : ∀ u, (excluded.insert items[pos]!).contains u = true ↔
                u ∈ items[pos]! :: ex := by
              intro u
              rw [Std.HashSet.contains_insert, Bool.or_eq_true, hex, beq_iff_eq, List.mem_cons]
              constructor
              · rintro (h | h)
                · exact Or.inl h.symm
                · exact Or.inr h
              · rintro (h | h)
                · exact Or.inl h.symm
                · exact Or.inr h
            have hinvE : Inv deps items.toList cap (items.toList.take (pos + 1)) inF
                (items[pos]! :: ex) := by rw [htake]; exact hinv.exclude ht'
            have hany : ∀ c : List Nat, c.any excluded.contains = c.any ex.contains := by
              intro c
              rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
              constructor
              · rintro ⟨u, hu, h⟩; exact ⟨u, hu, contains_iff.mpr ((hex u).mp h)⟩
              · rintro ⟨u, hu, h⟩; exact ⟨u, hu, (hex u).mpr (contains_iff.mp h)⟩
            cases hc : closure items[pos]! with
            | none =>
              rw [hc] at h
              obtain ⟨st2, hst2, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
              simp only [pure, Except.pure, Except.ok.injEq] at hst2
              subst hst2
              rw [ih _ _ _ _ _ _ _ hcur hex' hinvE h, hb1]
              rfl
            | some c =>
              rw [hc] at h
              dsimp only at h ⊢
              rw [hany c] at h
              split at h
              · rename_i hcond
                rw [ite_eq_left hcond]
                obtain ⟨st2, hst2, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
                simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
                obtain ⟨hinv', -⟩ := hinv.include hctx hitems ht' hc hcond.1 hcond.2
                rw [ih _ _ _ _ _ _ _ hcur hex' hinvE h,
                  ih _ _ _ _ _ _ _ (by rw [foldl_weight, hcur, wsum_append]) hex
                    (by rw [htake]; exact hinv') hst2, hb1]
              · rename_i hcond
                rw [ite_eq_right hcond]
                obtain ⟨st2, hst2, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
                simp only [pure, Except.pure, Except.ok.injEq] at hst2
                subst hst2
                rw [ih _ _ _ _ _ _ _ hcur hex' hinvE h, hb1]
                rfl

/-! ## The first tier -/

theorem tierOrder_trans (weight : Nat → Nat) (a b c : Nat) (h₁ : tierOrder weight a b = true)
    (h₂ : tierOrder weight b c = true) : tierOrder weight a c = true := by
  simp only [tierOrder, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
  omega

theorem tierOrder_total (weight : Nat → Nat) (a b : Nat) :
    (tierOrder weight a b || tierOrder weight b a) = true := by
  simp only [tierOrder, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- The search order is sorted: weight descending, then ID ascending. -/
theorem tierItems_sorted (weight : Nat → Nat) (topo : List Nat) :
    (topo.mergeSort (tierOrder weight)).Pairwise (fun a b => tierOrder weight a b = true) :=
  List.pairwise_mergeSort (tierOrder_trans weight) (tierOrder_total weight) topo

theorem Feasible.congr {deps : Nat → List Nat} {items items' : List Nat} {cap : Nat}
    {G G' : List Nat} (hi : ∀ x, x ∈ items ↔ x ∈ items') (hG : G.Perm G')
    (h : Feasible deps items cap G) : Feasible deps items' cap G' := by
  obtain ⟨hnd, hmem, hcl, hlen⟩ := h
  refine ⟨hG.nodup_iff.mp hnd, fun x hx => (hi x).mp (hmem x (hG.mem_iff.mpr hx)),
    fun u hu d hd => hG.mem_iff.mp (hcl u (hG.mem_iff.mpr hu) d hd), ?_⟩
  rw [← hG.length_eq]
  exact hlen

/-- **The first tier.** `firstTier topo weight deps cap` returns (ascending) a
set of terms of `topo` that is closed under `deps`, has at most `cap`
terms, and has the maximum total weight among all such sets; every such set
of the same weight is the same set or comes after it in the tie order over
the terms sorted by weight descending, then ID ascending (at the first term
in that order where they differ, the returned set contains it). -/
theorem firstTier_spec {topo : Array Nat} {weight : Nat → Nat} {deps : Nat → List Nat}
    {cap : Nat} {limits : Limits} {tier : Array Nat} {states : Nat}
    (h : firstTier topo weight deps cap limits = .ok (tier, states)) :
    Feasible deps topo.toList cap tier.toList ∧ tier.toList.Pairwise (· ≤ ·) ∧
      (∀ G, Feasible deps topo.toList cap G → wsum weight G ≤ wsum weight tier.toList) ∧
      ∀ G, Feasible deps topo.toList cap G → wsum weight G = wsum weight tier.toList →
        (∀ x, x ∈ G ↔ x ∈ tier.toList) ∨
          PrecIn (topo.toList.mergeSort (tierOrder weight)) tier.toList G := by
  unfold firstTier at h
  obtain ⟨cl, hcl, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
  obtain ⟨st, hst, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
  obtain ⟨hnd, hok, hdeps⟩ := tierClosures_spec hcl
  generalize hitemsL : topo.toList.mergeSort (tierOrder weight) = itemsL at h hst ⊢
  have hperm : itemsL.Perm topo.toList := hitemsL ▸ List.mergeSort_perm _ _
  have hmemI : ∀ x, x ∈ itemsL ↔ x ∈ topo.toList := fun x => hperm.mem_iff
  have hctx : Ctx deps (fun t => cl.getD t none) cap (itemsL.toArray).toList := by
    exact ⟨hperm.nodup_iff.mpr hnd, fun t ht => hok t ((hmemI t).mp ht),
      fun t ht d hd => (hmemI d).mpr (hdeps t ((hmemI t).mp ht) d hd)⟩
  have hsort : (itemsL.toArray).toList.Pairwise fun a b => weight b ≤ weight a := by
    rw [← hitemsL]
    refine (tierItems_sorted weight topo.toList).imp fun {a b} hab => ?_
    simp only [tierOrder, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at hab
    omega
  have hinv0 : Inv deps (itemsL.toArray).toList cap ((itemsL.toArray).toList.take 0) [] [] :=
    ⟨List.nodup_nil, by simp, by simp, by simp, by simp, fun _ h => by cases h⟩
  have hspec := tierDfs_spec hctx weight hsort limits _ 0 0 [] {} [] {} st (by simp [wsum])
    (fun u => by simp) hinv0 hst
  simp only [List.drop_zero] at hspec
  have hsplit : itemsL = [] ++ itemsL := rfl
  have hinvE : Inv deps itemsL cap [] [] [] :=
    ⟨List.nodup_nil, by simp, by simp, by simp, by simp, fun _ h => by cases h⟩
  have hord := leaves_order hctx itemsL [] [] [] hsplit hinvE
  obtain ⟨hne, hres⟩ := fold_best weight itemsL _ none hord (fun _ _ h => nomatch h)
  have hbest : st.best ≠ none := by
    rw [hspec]
    exact hne (Or.inr (leaves_ne_nil _ _ _ _ _))
  obtain ⟨b, R, hbR⟩ : ∃ b R, st.best = some (b, R) := by
    cases h' : st.best with
    | none => exact absurd h' hbest
    | some p => exact ⟨p.1, p.2, rfl⟩
  rw [hbR] at h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  rw [hspec] at hbR
  obtain ⟨hbw, hRmem, hle, -, htie⟩ := hres b R hbR
  have hRL : R ∈ tierLeaves (fun t => cl.getD t none) cap itemsL [] [] := by
    rcases hRmem with h | h
    · exact h
    · cases h
  obtain ⟨_, _, _, _, hleaf⟩ := leaves_shape hctx itemsL [] [] [] hsplit hinvE R hRL
  obtain ⟨hRnd, hRlen, -, hRitems, hRcl⟩ := hleaf
  have hTperm : R.Perm (R.mergeSort (· ≤ ·)) := (List.mergeSort_perm _ _).symm
  have hFeasR : Feasible deps itemsL cap R := ⟨hRnd, hRitems, hRcl, hRlen⟩
  have hwT : wsum weight (R.mergeSort (· ≤ ·)) = b := by rw [← wsum_perm hTperm, hbw]
  -- every feasible set is a leaf, up to order
  have hleaf : ∀ G, Feasible deps topo.toList cap G →
      ∃ F ∈ tierLeaves (fun t => cl.getD t none) cap itemsL [] [],
        (∀ x, x ∈ F ↔ x ∈ G) ∧ wsum weight F = wsum weight G := by
    intro G hG
    have hG' : Feasible deps itemsL cap G :=
      hG.congr (fun x => (hmemI x).symm) (List.Perm.refl G)
    obtain ⟨F, hF, hFG⟩ := leaves_complete hctx hG' itemsL [] [] [] hsplit hinvE (by simp)
      (by simp) (by simp)
    obtain ⟨_, _, _, _, hFnd, _⟩ := leaves_shape hctx itemsL [] [] [] hsplit hinvE F hF
    exact ⟨F, hF, hFG, wsum_perm ((List.perm_ext_iff_of_nodup hFnd hG.1).mpr hFG)⟩
  refine ⟨hFeasR.congr hmemI hTperm, ?_, fun G hG => ?_, fun G hG hGw => ?_⟩
  · exact (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
      (fun a b c h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
      (fun a b => by rcases Nat.le_total a b with h | h <;> simp [h]) R).imp
      fun h => of_decide_eq_true h
  · obtain ⟨F, hF, -, hw⟩ := hleaf G hG
    rw [hwT, ← hw]
    exact hle F hF
  · obtain ⟨F, hF, hFG, hw⟩ := hleaf G hG
    rw [hwT] at hGw
    rcases htie F hF (by omega) with rfl | hprec
    · exact Or.inl fun x => (hFG x).symm.trans hTperm.mem_iff
    · exact Or.inr (hprec.congr (fun x => hTperm.mem_iff) hFG)

/-- A successful first-tier search saw every term once. -/
theorem firstTier_nodup {topo : Array Nat} {weight : Nat → Nat} {deps : Nat → List Nat}
    {cap : Nat} {limits : Limits} {r : Array Nat × Nat}
    (h : firstTier topo weight deps cap limits = .ok r) : topo.toList.Nodup := by
  unfold firstTier at h
  obtain ⟨cl, hcl, -⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
  exact (tierClosures_spec hcl).1

/-! ## Phase 2 -/

/-- The position map of `respectsDeps` maps a term to an index holding it. -/
theorem posMap_spec (order : Array Nat) :
    ∀ (l : List (Nat × Nat)) (mp : Std.HashMap Nat Nat),
      (∀ d j, mp.get? d = some j → order[j]? = some d) → (∀ x ∈ l, order[x.2]? = some x.1) →
      ∀ d j, (l.foldl (fun m (x : Nat × Nat) => m.insert x.1 x.2) mp).get? d = some j →
        order[j]? = some d := by
  intro l
  induction l with
  | nil => intro mp hmp _ d j h; exact hmp d j h
  | cons x l ih =>
    intro mp hmp hl
    simp only [List.foldl_cons]
    refine ih _ (fun d j h => ?_) (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    rw [Std.HashMap.get?_insert] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      rw [beq_iff_eq] at hx
      subst hx
      exact hl x List.mem_cons_self
    · exact hmp d j h

/-- **Backwardness check.** If `respectsDeps` accepts `order`, every
dependency of the term at index `k` is at an index below `k`. -/
theorem respectsDeps_spec {order : Array Nat} {deps : Nat → List Nat}
    (h : respectsDeps order deps = true) :
    ∀ k (hk : k < order.size), ∀ d ∈ deps order[k], ∃ j, j < k ∧ order[j]? = some d := by
  intro k hk d hd
  unfold respectsDeps at h
  simp only at h
  rw [Array.all_eq_true_iff_forall_mem] at h
  have hmem : (order[k], k) ∈ order.zipIdx :=
    Array.mem_zipIdx_iff_getElem?.mpr (by simp [hk])
  have h1 := h _ hmem
  simp only [List.all_eq_true] at h1
  have h2 := h1 d hd
  cases hp : (order.zipIdx.foldl (fun m (x : Nat × Nat) => m.insert x.1 x.2)
      (∅ : Std.HashMap Nat Nat)).get? d with
  | none =>
    simp only [hp, Option.any_none] at h2
    cases h2
  | some j =>
    simp only [hp, Option.any_some, decide_eq_true_eq] at h2
    refine ⟨j, h2, ?_⟩
    rw [← Array.foldl_toList] at hp
    exact posMap_spec order _ ∅ (fun d j h => by simp at h)
      (fun x hx => Array.mem_zipIdx_iff_getElem?.mp (Array.mem_toList_iff.mp hx)) d j hp

/-- The reference counts of `shareCounts`: the occurrences of each index
among the Share indices of the expressions. -/
theorem shareCounts_inner :
    ∀ (l : List Nat) (refs : Array Nat),
      (l.foldl (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs).size =
          refs.size ∧
        ∀ i, i < refs.size →
          (l.foldl (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs)
            refs)[i]! = refs[i]! + l.count i := by
  intro l
  induction l with
  | nil => intro refs; simp
  | cons c cs ih =>
    intro refs
    simp only [List.foldl_cons]
    split
    · rename_i hc
      obtain ⟨hs, hv⟩ := ih (refs.modify c (· + 1))
      refine ⟨by rw [hs]; simp, fun i hi => ?_⟩
      rw [hv i (by simp; omega), List.count_cons]
      have hm : (refs.modify c (· + 1))[i]! = refs[i]! + (if c = i then 1 else 0) := by
        simp only [getElem!_def, Array.getElem?_modify]
        by_cases hci : c = i
        · subst hci; simp [Array.getElem?_eq_getElem hi]
        · simp [hci]
      rw [hm]
      by_cases hci : c = i
      · subst hci; simp; omega
      · have : (c == i) = false := by rw [beq_eq_false_iff_ne]; exact hci
        simp [hci, this]
    · rename_i hc
      obtain ⟨hs, hv⟩ := ih refs
      refine ⟨hs, fun i hi => ?_⟩
      rw [hv i hi, List.count_cons]
      have : (c == i) = false := by rw [beq_eq_false_iff_ne]; omega
      simp [this]

theorem shareCounts_spec (m : Nat) (exprs : Array Ixon.Expr) :
    (shareCounts m exprs).size = m ∧ ∀ i, i < m →
      (shareCounts m exprs)[i]! =
        (exprs.toList.flatMap fun e => (shareIndices e #[]).toList).count i := by
  unfold shareCounts
  rw [← Array.foldl_toList]
  suffices ∀ (l : List Ixon.Expr) (refs : Array Nat),
      (l.foldl (fun refs e => (shareIndices e #[]).foldl
        (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs) refs).size =
          refs.size ∧
        ∀ i, i < refs.size → (l.foldl (fun refs e => (shareIndices e #[]).foldl
          (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs) refs)[i]! =
            refs[i]! + (l.flatMap fun e => (shareIndices e #[]).toList).count i by
    obtain ⟨hs, hv⟩ := this exprs.toList (Array.replicate m 0)
    refine ⟨by rw [hs]; simp, fun i hi => ?_⟩
    rw [hv i (by simp; omega)]
    simp [hi]
  intro l
  induction l with
  | nil => intro refs; simp
  | cons e es ih =>
    intro refs
    simp only [List.foldl_cons, List.flatMap_cons, List.count_append]
    rw [← Array.foldl_toList]
    obtain ⟨hs1, hv1⟩ := shareCounts_inner (shareIndices e #[]).toList refs
    obtain ⟨hs2, hv2⟩ := ih ((shareIndices e #[]).toList.foldl
      (fun refs i => if i < refs.size then refs.modify i (· + 1) else refs) refs)
    refine ⟨by rw [hs2, hs1], fun i hi => ?_⟩
    rw [hv2 i (by rw [hs1]; exact hi), hv1 i hi]
    omega

/-- Inserting keys `f i` for `i` in a duplicate-free list with injective `f`:
each key holds its own value. -/
theorem fold_insert_getD {β : Type} (f : Nat → Nat) (g : Nat → β) (fb : β) :
    ∀ (l : List Nat) (mp : Std.HashMap Nat β), l.Nodup →
      (∀ i ∈ l, ∀ j ∈ l, f i = f j → i = j) →
      ∀ i ∈ l, (l.foldl (fun m i => m.insert (f i) (g i)) mp).getD (f i) fb = g i := by
  have keep : ∀ (l : List Nat) (mp : Std.HashMap Nat β) (k : Nat), (∀ i ∈ l, f i ≠ k) →
      (l.foldl (fun m i => m.insert (f i) (g i)) mp).getD k fb = mp.getD k fb := by
    intro l
    induction l with
    | nil => intro mp k _; rfl
    | cons a l ih =>
      intro mp k hk
      simp only [List.foldl_cons]
      rw [ih _ k (fun i hi => hk i (List.mem_cons_of_mem _ hi)), Std.HashMap.getD_insert]
      have : (f a == k) = false := by
        rw [beq_eq_false_iff_ne]; exact hk a List.mem_cons_self
      rw [this]
      rfl
  intro l
  induction l with
  | nil => intro _ _ _ i hi; cases hi
  | cons a l ih =>
    intro mp hnd hinj i hi
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [keep _ _ _ (fun j hj hfj => hnd.1 (hinj j (List.mem_cons_of_mem _ hj) i
        List.mem_cons_self hfj ▸ hj)), Std.HashMap.getD_insert]
      simp
    · exact ih _ hnd.2 (fun j hj k hk h => hinj j (List.mem_cons_of_mem _ hj) k
        (List.mem_cons_of_mem _ hk) h) i hi

theorem getBang_inj {order : Array Nat} (hnd : order.toList.Nodup) {i j : Nat}
    (hi : i < order.size) (hj : j < order.size) (h : order[i]! = order[j]!) : i = j := by
  rw [getElem!_pos order i hi, getElem!_pos order j hj] at h
  have hi' : i < order.toList.length := by simpa using hi
  have hj' : j < order.toList.length := by simpa using hj
  have e1 := hnd.idxOf_getElem i hi'
  have e2 := hnd.idxOf_getElem j hj'
  have : order.toList[i] = order.toList[j] := by simpa using h
  rw [this] at e1
  omega

/-- **Reference counts.** The weight of the stored term at phase-1 index
`i` is the number of `Share(i)` in the phase-1 entries and roots. -/
theorem tierWeights_spec {order1 : Array Nat} (hnd : order1.toList.Nodup)
    (entries1 roots1 : Array Ixon.Expr) {i : Nat} (hi : i < order1.size) :
    (tierWeights order1 entries1 roots1).getD order1[i] 0 =
      ((entries1.toList ++ roots1.toList).flatMap fun e => (shareIndices e #[]).toList).count i := by
  unfold tierWeights
  have := fold_insert_getD (fun i => order1[i]!) (fun i => (shareCounts order1.size
    (entries1 ++ roots1))[i]!) 0 (List.range order1.size) {} List.nodup_range
    (fun a ha b hb h => getBang_inj hnd (List.mem_range.mp ha) (List.mem_range.mp hb) h) i
    (List.mem_range.mpr hi)
  rw [← getElem!_pos order1 i hi, this, (shareCounts_spec _ _).2 i hi]
  simp

/-- The terms a phase-1 body references. -/
theorem mem_bodyRefs (order1 : Array Nat) (e : Ixon.Expr) (d : Nat) :
    d ∈ bodyRefs order1 e ↔ ∃ j ∈ (shareIndices e #[]).toList, order1[j]? = some d := by
  unfold bodyRefs
  simp [List.mem_filterMap]

/-- **Dependencies.** The dependencies of the stored term at phase-1 index
`i` are the terms its phase-1 body references. -/
theorem tierDeps_spec {order1 : Array Nat} (hnd : order1.toList.Nodup)
    (entries1 : Array Ixon.Expr) {i : Nat} (hi : i < order1.size) :
    (tierDeps order1 entries1).getD order1[i] [] = bodyRefs order1 (entries1[i]?.getD default) := by
  unfold tierDeps
  have := fold_insert_getD (fun i => order1[i]!) (fun i => bodyRefs order1
    (entries1[i]?.getD default)) [] (List.range order1.size) {} List.nodup_range
    (fun a ha b hb h => getBang_inj hnd (List.mem_range.mp ha) (List.mem_range.mp hb) h) i
    (List.mem_range.mpr hi)
  rw [← getElem!_pos order1 i hi, this]

/-- **Phase 2.** A successful slot allocation on the phase-1 table `order1`
(entries `entries1`, roots `roots1`), with the reference counts `weight`
and the body-reference relation `deps` of the phase-1 output
(`tierWeights_spec`, `tierDeps_spec`):
* the first tier is a maximum-reference-count set of at most 8 stored terms
  closed under body references, and the first such set in the tie order
  (`firstTier_spec`);
* the final order is a permutation of the phase-1 table that places every
  body reference of an entry before it (backwardness);
* it is the phase-1 order if the guard kept it, otherwise the first tier in
  the pinned order followed by the other terms in the Kahn priority order,
  and its reference cost is at most the phase-1 order's. -/
theorem allocate_spec {layout : ShareLayout} {limits : Limits} {dag : Dag} {deg : Array Nat}
    {order1 : Array Nat} {entries1 roots1 : Array Ixon.Expr} {a : Allocation}
    (h : allocate layout limits dag deg order1 entries1 roots1 = .ok a) :
    let weight := fun t => (tierWeights order1 entries1 roots1).getD t 0
    let deps := fun t => (tierDeps order1 entries1).getD t []
    let cap := min 8 order1.size
    order1.toList.Nodup ∧
    (Feasible deps order1.toList cap a.tier.toList ∧ a.tier.toList.Pairwise (· ≤ ·) ∧
      (∀ G, Feasible deps order1.toList cap G → wsum weight G ≤ wsum weight a.tier.toList) ∧
      ∀ G, Feasible deps order1.toList cap G → wsum weight G = wsum weight a.tier.toList →
        (∀ x, x ∈ G ↔ x ∈ a.tier.toList) ∨
          PrecIn (order1.toList.mergeSort (tierOrder weight)) a.tier.toList G) ∧
    a.order.toList.Perm order1.toList ∧
    (∀ k (hk : k < a.order.size), ∀ d ∈ deps a.order[k], ∃ j, j < k ∧ a.order[j]? = some d) ∧
    (a.order = if a.kept then order1 else pinnedOrder dag deg a.tier ++
      kahnOrder weight deps ((order1.toList.mergeSort (· ≤ ·)).toArray.filter
        (!a.tier.contains ·))) ∧
    a.refCost1 = refCost layout weight order1 ∧ a.refCostFinal = refCost layout weight a.order ∧
    a.refCostFinal ≤ a.refCost1 ∧
    (pinnedOrder dag deg a.tier ++ kahnOrder weight deps
      ((order1.toList.mergeSort (· ≤ ·)).toArray.filter (!a.tier.contains ·))).toList.Perm
      order1.toList ∧
    a.refCostFinal ≤ refCost layout weight (pinnedOrder dag deg a.tier ++ kahnOrder weight deps
      ((order1.toList.mergeSort (· ≤ ·)).toArray.filter (!a.tier.contains ·))) := by
  intro weight deps cap
  unfold allocate at h
  dsimp only at h
  obtain ⟨⟨tier, states⟩, hft, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
  dsimp only at h
  obtain ⟨_, hc2, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
  try dsimp only at h
  obtain ⟨_, hc1, h⟩ := Ix.Sharing.Verify.SharingExact.bind_eq_ok h
  have hresp := checkInternal_ok hc1
  have hperm := checkInternal_ok hc2
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hnd := firstTier_nodup hft
  -- the sorted pinned order equals the sorted phase-1 table
  have hperm2 : (pinnedOrder dag deg tier ++ kahnOrder weight deps
      ((order1.toList.mergeSort (· ≤ ·)).toArray.filter (!tier.contains ·))).toList.Perm
      order1.toList := by
    have hs := congrArg Array.toList (beq_iff_eq.mp hperm)
    simp only at hs
    refine (List.mergeSort_perm _ (fun x1 x2 => decide (x1 ≤ x2))).symm.trans ?_
    rw [hs]
    exact List.mergeSort_perm _ _
  refine ⟨hnd, firstTier_spec hft, ?_, respectsDeps_spec hresp, by dsimp only, by dsimp only,
    by dsimp only, ?_, hperm2, ?_⟩
  · dsimp only
    split
    · exact List.Perm.refl _
    · exact hperm2
  · simp only
    split
    · exact Nat.le_refl _
    · rename_i hk
      simp only [Bool.not_eq_true, decide_eq_false_iff_not, Nat.not_lt] at hk
      exact hk
  · simp only
    split
    · rename_i hk
      simp only [decide_eq_true_eq] at hk
      exact Nat.le_of_lt hk
    · exact Nat.le_refl _

end Ix.Sharing.Verify.Tiered
