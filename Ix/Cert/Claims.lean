import Ix.Cert.PassHooks
import Ix.CompileCert.MutualArtifact
import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.Canon.Refine

/-! # The names a block's compile claims (Route A, B9b, `HookFree`'s discharge, step 3)

A block's compile (`Ix.runBlockWithAux`) claims the names of its result's
projections (`Ix.Cert.Resolution.claimWrites`), or its key when there are
none. This file shows, with Pass 3's hooks in any state, that each of them
is a member's name or the name of a constructor an inductive member lists:

* the class sort (`Ix.Compile.Canon.sortClasses`) only regroups its members
  (`sortClasses_mem`), for any member names: the comparisons' answers do not
  matter;
* ... -/

namespace Ix.Cert.Claims

open Ix Ix.CompileM Ix.Compile.Canon

/-! ## The class sort keeps its members -/

section sort

variable {α β : Type}

/-- Every successful run of a comparison computation returns a value
satisfying `p`. -/
def CmpPost (p : α → Prop) (x : CmpM α) : Prop :=
  ∀ s v s', x.run s = .ok (v, s') → p v

theorem CmpPost.pure {p : α → Prop} {a : α} (h : p a) : CmpPost p (Pure.pure a : CmpM α) := by
  intro s v s' hr
  cases hr
  exact h

theorem CmpPost.bind {x : CmpM α} {f : α → CmpM β} {q : α → Prop} {p : β → Prop}
    (hx : CmpPost q x) (hf : ∀ a, q a → CmpPost p (f a)) : CmpPost p (x >>= f) := by
  intro s v s' hr
  rw [StateT.run_bind] at hr
  cases h : x.run s with
  | error e => rw [h] at hr; cases hr
  | ok r => rw [h] at hr; exact hf r.1 (hx s r.1 r.2 h) r.2 v s' hr

theorem CmpPost.bindAny {x : CmpM α} {f : α → CmpM β} {p : β → Prop}
    (hf : ∀ a, CmpPost p (f a)) : CmpPost p (x >>= f) :=
  CmpPost.bind (q := fun _ => True) (fun _ _ _ _ => trivial) fun a _ => hf a

theorem CmpPost.liftE_error {p : α → Prop} (e : CmpError) : CmpPost p (liftE (.error e) : CmpM α) := by
  intro s v s' hr
  cases hr

/-- Elements satisfying `M`, in every list of a list. -/
def AllIn (M : α → Prop) (xss : List (List α)) : Prop := ∀ xs ∈ xss, ∀ x ∈ xs, M x

theorem mergeM_post (cmp : α → α → CmpM Ordering) (M : α → Prop) :
    ∀ (n : Nat) (as bs : List α), as.length + bs.length ≤ n → (∀ x ∈ as, M x) → (∀ x ∈ bs, M x) →
      CmpPost (fun r => ∀ y ∈ r, M y) (List.mergeM cmp as bs) := by
  intro n
  induction n with
  | zero =>
    intro as bs hl has hbs
    cases as <;> cases bs <;> simp at hl
    rw [List.mergeM.eq_def]
    exact CmpPost.pure (by simp)
  | succ n ih =>
    intro as bs hl has hbs
    cases as with
    | nil => rw [List.mergeM.eq_def]; exact CmpPost.pure hbs
    | cons a as' =>
      cases bs with
      | nil => rw [List.mergeM.eq_def]; exact CmpPost.pure has
      | cons b bs' =>
        rw [List.mergeM.eq_def]
        simp only
        refine CmpPost.bindAny fun o => ?_
        split
        · refine CmpPost.bind (ih (a :: as') bs' (by simp at hl ⊢; omega) has
            (fun x hx => hbs x (by simp [hx]))) fun merged hm => CmpPost.pure ?_
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hbs _ (by simp)
          · exact hm y hy
        · refine CmpPost.bind (ih as' (b :: bs') (by simp at hl ⊢; omega)
            (fun x hx => has x (by simp [hx])) hbs) fun merged hm => CmpPost.pure ?_
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact has _ (by simp)
          · exact hm y hy

theorem mergePairsM_post (cmp : α → α → CmpM Ordering) (M : α → Prop) :
    ∀ (n : Nat) (xss : List (List α)), xss.length ≤ n → AllIn M xss →
      CmpPost (AllIn M) (List.mergePairsM cmp xss) := by
  intro n
  induction n with
  | zero =>
    intro xss hl h
    cases xss with
    | nil => rw [List.mergePairsM.eq_def]; exact CmpPost.pure h
    | cons _ _ => simp at hl
  | succ n ih =>
    intro xss hl h
    match xss with
    | a :: b :: xs =>
      rw [List.mergePairsM.eq_def]
      simp only
      refine CmpPost.bind (mergeM_post cmp M _ a b (Nat.le_refl _) (h a (by simp)) (h b (by simp)))
        fun merged hm => CmpPost.bind (ih xs (by simp at hl; omega)
          (fun l hl' => h l (by simp [hl']))) fun rest hr => CmpPost.pure ?_
      intro l hl'
      rcases List.mem_cons.1 hl' with rfl | hl'
      · exact hm
      · exact hr l hl'
    | [] => rw [List.mergePairsM.eq_def]; exact CmpPost.pure h
    | [a] => rw [List.mergePairsM.eq_def]; exact CmpPost.pure h

theorem mergeAllMFuel_post (cmp : α → α → CmpM Ordering) (M : α → Prop) :
    ∀ (fuel : Nat) (xss : List (List α)), AllIn M xss →
      CmpPost (fun r => ∀ y ∈ r, M y) (List.mergeAllMFuel cmp fuel xss) := by
  intro fuel
  induction fuel with
  | zero =>
    intro xss h
    rw [List.mergeAllMFuel.eq_def]
    exact CmpPost.pure fun y hy => by
      obtain ⟨l, hl, hy⟩ := List.mem_flatten.1 hy
      exact h l hl y hy
  | succ fuel ih =>
    intro xss h
    match xss with
    | [x] =>
      rw [List.mergeAllMFuel.eq_def]
      exact CmpPost.pure (h x (by simp))
    | [] =>
      rw [List.mergeAllMFuel.eq_def]
      exact CmpPost.bind (mergePairsM_post cmp M _ [] (Nat.le_refl _) h) fun r hr => ih r hr
    | a :: b :: xs =>
      rw [List.mergeAllMFuel.eq_def]
      exact CmpPost.bind (mergePairsM_post cmp M _ _ (Nat.le_refl _) h) fun r hr => ih r hr

theorem runs_post (cmp : α → α → CmpM Ordering) (M : α → Prop) : ∀ m : Nat,
    (∀ xs : List α, 2 * xs.length < m → (∀ x ∈ xs, M x) →
      CmpPost (AllIn M) (List.sequencesM cmp xs)) ∧
    (∀ (a : α) (as xs : List α), 2 * xs.length + 1 < m → (∀ x ∈ a :: as, M x) → (∀ x ∈ xs, M x) →
      CmpPost (AllIn M) (List.descendingM cmp a as xs)) ∧
    (∀ (a : α) (f : List α → List α) (xs : List α),
      (∀ ys, (∀ y ∈ ys, M y) → ∀ y ∈ f ys, M y) → 2 * xs.length + 1 < m → M a → (∀ x ∈ xs, M x) →
      CmpPost (AllIn M) (List.ascendingM cmp a f xs)) := by
  intro m
  induction m with
  | zero => exact ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨ihS, ihD, ihA⟩ := ih
    refine ⟨fun xs hl hxs => ?_, fun a as xs hl ha hxs => ?_, fun a f xs hf hl ha hxs => ?_⟩
    · match xs with
      | a :: b :: xs =>
        rw [List.sequencesM.eq_def]
        simp only
        refine CmpPost.bindAny fun o => ?_
        split
        · exact ihD b [a] xs (by simp at hl ⊢; omega) (by simp [hxs a (by simp), hxs b (by simp)])
            (fun x hx => hxs x (by simp [hx]))
        · refine ihA b (fun ys => a :: ys) xs (fun ys hys y hy => ?_) (by simp at hl ⊢; omega)
            (hxs b (by simp)) (fun x hx => hxs x (by simp [hx]))
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hxs _ (by simp)
          · exact hys y hy
      | [] => rw [List.sequencesM.eq_def]; exact CmpPost.pure (by simp [AllIn])
      | [a] =>
        rw [List.sequencesM.eq_def]
        exact CmpPost.pure fun l hl' y hy => by simp at hl'; subst hl'; exact hxs y hy
    · match xs with
      | b :: bs =>
        rw [List.descendingM.eq_def]
        simp only
        refine CmpPost.bindAny fun o => ?_
        split
        · exact ihD b (a :: as) bs (by simp at hl ⊢; omega)
            (by intro x hx; simp at hx; rcases hx with rfl | rfl | hx
                · exact hxs _ (by simp)
                · exact ha _ (by simp)
                · exact ha x (by simp [hx]))
            (fun x hx => hxs x (by simp [hx]))
        · refine CmpPost.bind (ihS (b :: bs) (by simp at hl ⊢; omega) hxs) fun rest hr =>
            CmpPost.pure ?_
          intro l hl' y hy
          rcases List.mem_cons.1 hl' with rfl | hl'
          · exact ha y hy
          · exact hr l hl' y hy
      | [] =>
        rw [List.descendingM.eq_def]
        simp only
        refine CmpPost.bind (ihS [] (by simp at hl ⊢; omega) (by simp)) fun rest hr =>
          CmpPost.pure ?_
        intro l hl' y hy
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact ha y hy
        · exact hr l hl' y hy
    · match xs with
      | b :: bs =>
        rw [List.ascendingM.eq_def]
        simp only
        refine CmpPost.bindAny fun o => ?_
        split
        · refine ihA b (fun ys => f (a :: ys)) bs (fun ys hys y hy => ?_) (by simp at hl ⊢; omega)
            (hxs b (by simp)) (fun x hx => hxs x (by simp [hx]))
          refine hf (a :: ys) (fun z hz => ?_) y hy
          rcases List.mem_cons.1 hz with rfl | hz
          · exact ha
          · exact hys z hz
        · refine CmpPost.bind (ihS (b :: bs) (by simp at hl ⊢; omega) hxs) fun rest hr =>
            CmpPost.pure ?_
          intro l hl' y hy
          rcases List.mem_cons.1 hl' with rfl | hl'
          · exact hf [a] (by simp [ha]) y hy
          · exact hr l hl' y hy
      | [] =>
        rw [List.ascendingM.eq_def]
        simp only
        refine CmpPost.bind (ihS [] (by simp at hl ⊢; omega) (by simp)) fun rest hr =>
          CmpPost.pure ?_
        intro l hl' y hy
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hf [a] (by simp [ha]) y hy
        · exact hr l hl' y hy

/-- A merge sort run with any comparison returns members of its input. -/
theorem sortByM_post (cmp : α → α → CmpM Ordering) (M : α → Prop) (xs : List α) (h : ∀ x ∈ xs, M x) :
    CmpPost (fun r => ∀ y ∈ r, M y) (List.sortByM xs cmp) := by
  unfold List.sortByM
  exact CmpPost.bind ((runs_post cmp M (2 * xs.length + 1)).1 xs (by omega) h) fun runs hr =>
    mergeAllMFuel_post cmp M _ runs hr

theorem groupByMAux_post (eq : α → α → CmpM Bool) (M : α → Prop) :
    ∀ (xs : List α) (gs : List (List α)), (∀ x ∈ xs, M x) → AllIn M gs →
      CmpPost (AllIn M) (List.groupByMAux eq xs gs) := by
  intro xs
  induction xs with
  | nil =>
    intro gs _ hg
    rw [List.groupByMAux.eq_def]
    exact CmpPost.pure fun l hl => hg l (List.mem_reverse.1 hl)
  | cons a as ih =>
    intro gs hxs hg
    match gs with
    | (ag :: g) :: gs =>
      rw [List.groupByMAux.eq_def]
      simp only
      refine CmpPost.bindAny fun o => ?_
      split
      · refine ih _ (fun x hx => hxs x (by simp [hx])) fun l hl => ?_
        rcases List.mem_cons.1 hl with rfl | hl
        · intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hxs _ (by simp)
          · exact hg _ (by simp) y hy
        · exact hg l (by simp [hl])
      · refine ih _ (fun x hx => hxs x (by simp [hx])) fun l hl => ?_
        simp only [List.mem_cons] at hl
        rcases hl with rfl | rfl | hl
        · intro y hy; simp at hy; subst hy; exact hxs _ (by simp)
        · intro y hy; exact hg _ (by simp) y (List.mem_reverse.1 hy)
        · exact hg l (by simp [hl])
    | [] :: gs =>
      rw [List.groupByMAux.eq_def]
      simp only
      exact CmpPost.pure fun l hl => hg l (by simpa using List.mem_reverse.1 hl)
    | [] =>
      rw [List.groupByMAux.eq_def]
      simp only
      exact CmpPost.pure fun l hl => by simp at hl

end sort

/-! ## The refinement rounds -/

theorem sortByName_mem {x : MutConst} {xs : List MutConst} (h : x ∈ sortByName xs) : x ∈ xs :=
  (Ix.CompileCert.Canon.sortByName_perm xs).mem_iff.1 h

theorem refineClass_post (addr? : Name → Option Address) (ctx : MutCtx) (M : MutConst → Prop)
    (xs : List MutConst) (h : ∀ x ∈ xs, M x) : CmpPost (AllIn M) (refineClass addr? ctx xs) := by
  match xs with
  | [] => exact CmpPost.liftE_error _
  | [x] => exact CmpPost.pure fun l hl y hy => by simp at hl; subst hl; exact h y hy
  | x :: y :: rest =>
    simp only [refineClass]
    refine CmpPost.bind (sortByM_post _ M _ h) fun sorted hs => ?_
    refine CmpPost.bind (groupByM_post sorted hs) fun groups hg => CmpPost.pure ?_
    intro l hl z hz
    obtain ⟨g, hg', rfl⟩ := List.mem_map.1 hl
    exact hg g hg' z (sortByName_mem hz)
where
  groupByM_post (sorted : List MutConst) (hs : ∀ y ∈ sorted, M y) :
      CmpPost (AllIn M) (List.groupByM (fun a b => do return (← compareConst addr? ctx a b) == .eq) sorted) := by
    match sorted with
    | [] => exact CmpPost.pure (by simp [AllIn])
    | a :: as =>
      exact groupByMAux_post _ M as [[a]] (fun x hx => hs x (by simp [hx]))
        (fun l hl y hy => by simp at hl; subst hl; simp at hy; subst hy; exact hs _ (by simp))

theorem refineClasses_post (addr? : Name → Option Address) (ctx : MutCtx) (M : MutConst → Prop) :
    ∀ (classes : List (List MutConst)), AllIn M classes →
      CmpPost (AllIn M) (refineClasses addr? ctx classes)
  | [], _ => CmpPost.pure (by simp [AllIn])
  | c :: cs, h => by
    simp only [refineClasses]
    refine CmpPost.bind (refineClass_post addr? ctx M c (h c (by simp))) fun gs hgs => ?_
    refine CmpPost.bind (refineClasses_post addr? ctx M cs fun l hl => h l (by simp [hl]))
      fun rest hr => CmpPost.pure ?_
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hgs l hl
    · exact hr l hl

theorem sortLoop_post (addr? : Name → Option Address) (M : MutConst → Prop) :
    ∀ (fuel round : Nat) (classes : List (List MutConst)), AllIn M classes →
      CmpPost (fun r => AllIn M r.1) (sortLoop addr? fuel round classes)
  | 0, _, _, _ => CmpPost.liftE_error _
  | fuel + 1, round, classes, h => by
    simp only [sortLoop]
    refine CmpPost.bind (refineClasses_post addr? _ M classes h) fun refined hr => ?_
    split
    · exact CmpPost.pure hr
    · exact sortLoop_post addr? M fuel (round + 1) refined hr

/-- **The class sort regroups its members**: every member of a class
`sortClasses` returns is one of its input's, for any rules, addresses and
member names. -/
theorem sortClasses_mem {rules : Rules} {addr? : Name → Option Address} {sources : List MutConst}
    {classes : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? sources = .ok (classes, stats)) :
    ∀ c ∈ classes, ∀ x ∈ c, x ∈ sources := by
  unfold sortClasses at h
  split at h
  · cases h; intro c hc; cases hc
  · have seed : ∀ x ∈ (match rules.seed with
        | .byNameHash => sortByName sources
        | .allOrder => sources), x ∈ sources := by
      intro x hx
      split at hx
      · exact sortByName_mem hx
      · exact hx
    obtain ⟨⟨⟨cl, rounds⟩, st⟩, hrun, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
    have post := sortLoop_post addr? (· ∈ sources) (sources.length + 1) 0 _
      (fun l hl x hx => by simp at hl; subst hl; exact seed x hx) {} _ _ hrun
    dsimp only at h
    repeat' (first | (cases h; done) | (split at h <;> try dsimp only at h))
    simp only [pure, Except.pure] at h
    injections
    subst_vars
    exact post

end Ix.Cert.Claims
