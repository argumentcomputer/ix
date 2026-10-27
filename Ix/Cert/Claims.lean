import Ix.Cert.BlockRecords
import Ix.CompileCert.MutualArtifact
import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.Canon.Refine

/-! # The names a block's compile claims

A block's compile (`Ix.runBlockWithAux`) claims the names of its result's
projections (`Ix.Cert.Resolution.claimWrites`), or its key when there are
none. This file shows that each of them is a member's name or the name of a
constructor an inductive member lists:

* the class sort (`Ix.Compile.Canon.sortClasses`) only regroups its members
  (`sortClasses_mem`), for any member names: the comparisons' answers do not
  matter, so no hypothesis on the names (`Canon.KeysDistinct`) is needed;
* a mutual block's projections carry its members' names and their
  constructors' (`mutualBlock_names`), and a lone constant other than an
  inductive or a constructor has none (`constantInfo_lone`);
* so `runBlock`'s projections carry those names (`runBlockWithAux_owned`,
  `runBlock_owned`). -/

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
    try dsimp only at h
    repeat' (first | (cases h; done) | (split at h <;> try dsimp only at h))
    simp only [pure, Except.pure] at h
    injections
    subst_vars
    exact post

/-! ## A block compile's projection names -/

section names

open Ix.CompileCert.Emission (Yields)
open Ix.CompileCert.MutualProjections (logicalRows expectedRows sourceRows)

/-- `x` is the name of a member of `sources` or of a constructor such a
member carries. -/
def SourceName (sources : List (List MutConst)) (x : Name) : Prop :=
  ∃ src, (∃ c ∈ sources, src ∈ c) ∧ (x = src.name ∨ ∃ ctor ∈ src.ctors, x = ctor.cnst.name)

theorem mem_of_mem_zipIdx {α : Type} {l : List α} {x : α} {i : Nat} (h : (x, i) ∈ l.zipIdx) : x ∈ l :=
  List.fst_mem_of_mem_zipIdx h

theorem expectedRows_name {owner : Address} {sources : List (List MutConst)} {x : Name}
    {c : Ixon.Constant} (h : (x, c) ∈ expectedRows owner sources) : SourceName sources x := by
  unfold expectedRows at h
  obtain ⟨⟨members, index⟩, hm, h⟩ := List.mem_flatMap.1 h
  obtain ⟨src, hsrc, h⟩ := List.mem_flatMap.1 h
  refine ⟨src, ⟨members, mem_of_mem_zipIdx hm, hsrc⟩, ?_⟩
  unfold sourceRows at h
  rcases List.mem_cons.1 h with h | h
  · exact .inl (Prod.mk.inj h).1
  · obtain ⟨⟨ctor, ci⟩, hci, he⟩ := List.mem_map.1 h
    exact .inr ⟨ctor, Array.mem_toList_iff.1 (mem_of_mem_zipIdx hci), (Prod.mk.inj he).1.symm⟩

theorem row_logical {rows : Array Ix.CompileCert.MutualProjections.Row} {row : Ix.CompileCert.MutualProjections.Row} (h : row ∈ rows) :
    (row.1, row.2.1) ∈ logicalRows rows :=
  List.mem_map.2 ⟨row, Array.mem_toList_iff.2 h, rfl⟩

/-- **A mutual block's projections carry its members' names and their
constructors'**: the wrapper's rows (`MutualProjections.build_rows`), or a
collapsed block's, every member registered to it
(`MutualProjections.standalone_rows`). -/
theorem mutualBlock_names (sources : List (List MutConst)) :
    Yields (compileMutualBlock sources) (fun out => ∀ row ∈ out.projections, SourceName sources row.1) := by
  refine Ix.CompileCert.ProjectionLayout.mutual_block _ sources ?_
  unfold compileMutualPayload
  refine Ix.CompileCert.Emission.Yields.bindAny _ fun compiled => ?_
  intro context before output after ran
  obtain ⟨-, -, built⟩ :=
    Ix.CompileCert.ProjectionLayout.finish_mutual_ok context sources compiled.1 compiled.2.2 ran
  obtain ⟨-, wrapped | collapsed⟩ :=
    Ix.CompileCert.MutualArtifact.build_cases _ sources compiled.1 compiled.2.2 before output built
  · obtain ⟨targets, metadata, -, -, proj⟩ := wrapped
    intro row hrow
    have hl := row_logical hrow
    rw [proj, Ix.CompileCert.MutualProjections.build_rows] at hl
    exact expectedRows_name hl
  · obtain ⟨-, -, rows⟩ := collapsed
    intro row hrow
    have hl := row_logical hrow
    rw [rows] at hl
    obtain ⟨src, hsrc, he⟩ := List.mem_map.1 hl
    obtain ⟨c, hc, hs⟩ := List.mem_flatten.1 hsrc
    exact ⟨src, ⟨c, hc, hs⟩, .inl (Prod.mk.inj he).1.symm⟩

/-- The block finisher returns no projections. -/
theorem finish_lone (info : Ixon.ConstantInfo) (blockMeta : Ixon.ConstantMeta) :
    Yields (finishConstantInfoWithSharing info blockMeta) (fun r => r.projections = #[]) := by
  intro context before output after ran
  rw [Ix.CompileCert.EmissionBlocks.finish_run] at ran
  cases built : buildConstantWithSharing context.1.sharingLimits info before.refs before.univs with
  | error e => rw [built] at ran; cases ran
  | ok block =>
    rw [built] at ran
    simp only [Except.map, Prod.mk.injEq, Except.ok.injEq] at ran
    obtain ⟨rfl, -⟩ := ran
    rfl

theorem definitionDataInfo_lone (source : Ix.Def) :
    Yields (compileDefinitionDataInfo source) (fun r => r.projections = #[]) := by
  unfold compileDefinitionDataInfo compileDefinitionDataBlock
  exact Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
    obtain ⟨a, b, c, e⟩ := d
    exact finish_lone _ _

/-- **A lone constant's compile returns no projections**, for every kind but
an inductive's and a constructor's (the block compile sends those through
the mutual compiler). -/
theorem constantInfo_lone (const : ConstantInfo) (hi : ∀ v, const = .inductInfo v → False)
    (hc : ∀ v, const = .ctorInfo v → False) :
    Yields (compileConstantInfo const) (fun r => r.projections = #[]) := by
  cases const with
  | defnInfo v =>
    show Yields (compileDefinitionConstantInfo v) _
    unfold compileDefinitionConstantInfo withMutCtx
    rw [Ix.CompileCert.EmissionDispatch.compileDefinitionInfo_eq]
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | thmInfo v =>
    show Yields (compileTheoremConstantInfo v) _
    unfold compileTheoremConstantInfo withMutCtx compileTheoremInfo
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | opaqueInfo v =>
    show Yields (compileOpaqueConstantInfo v) _
    unfold compileOpaqueConstantInfo withMutCtx compileOpaqueInfo
    exact Yields.withBlockEnv _ (definitionDataInfo_lone _)
  | axiomInfo v =>
    show Yields (compileConstantInfoCore (.axiomInfo v)) _
    unfold compileConstantInfoCore withMutCtx
    refine Yields.withBlockEnv _ ?_
    show Yields (compileAxiomInfo v) _
    unfold compileAxiomInfo compileAxiomBlock
    exact Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone _ _
  | quotInfo v =>
    show Yields (compileQuotientConstantInfo v) _
    unfold compileQuotientConstantInfo withMutCtx compileQuotientInfo compileQuotientBlock
    exact Yields.withBlockEnv _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone _ _)
  | recInfo v =>
    show Yields (compileRecursorConstantInfo v) _
    unfold compileRecursorConstantInfo withMutCtx compileRecursorInfo compileRecursorBlock
    exact Yields.withBlockEnv _ (Yields.bindAny _ fun _ => Yields.bindAny _ fun d => by
      obtain ⟨a, b, c⟩ := d
      exact finish_lone _ _)
  | inductInfo v => exact absurd rfl (hi v)
  | ctorInfo v => exact absurd rfl (hc v)

end names

/-! ## The members a block compile reads -/

section members

open Ix.CompileCert (rawRun rawRun_pure bind_ok)

variable {α β γ σ : Type}

/-- Every successful run from the context `ctx` returns a value satisfying
`P`. -/
def RunPost (ctx : CompileEnv × BlockEnv) (P : α → Prop) (x : CompileM α) : Prop :=
  ∀ s v s', rawRun x ctx s = (.ok v, s') → P v

theorem RunPost.pure {ctx : CompileEnv × BlockEnv} {P : α → Prop} {a : α} (h : P a) :
    RunPost ctx P (Pure.pure a) := by
  intro s v s' hr
  rw [rawRun_pure] at hr
  cases hr
  exact h

theorem RunPost.bind {ctx : CompileEnv × BlockEnv} {x : CompileM α} {f : α → CompileM β} {q : α → Prop}
    {p : β → Prop} (hx : RunPost ctx q x) (hf : ∀ a, q a → RunPost ctx p (f a)) : RunPost ctx p (x >>= f) := by
  intro s v s' hr
  obtain ⟨a, m, ha, hb⟩ := bind_ok hr
  exact hf a (hx s a m ha) m v s' hb

theorem RunPost.throw {ctx : CompileEnv × BlockEnv} {P : α → Prop} (e : CompileError) :
    RunPost ctx P (throw e : CompileM α) := by
  intro s v s' hr
  rw [Ix.CompileCert.rawRun_throw] at hr
  cases hr

theorem RunPost.findConst (ctx : CompileEnv × BlockEnv) (n : Name) :
    RunPost ctx (fun c => ctx.1.env.get? n = some c) (findConst n) :=
  fun _ _ _ hr => Ix.Cert.BlockRecords.findConst_ok hr

/-- A loop over a list keeps an invariant its body keeps. -/
theorem RunPost.forIn (ctx : CompileEnv × BlockEnv) (I : σ → Prop) (body : γ → σ → CompileM (ForInStep σ)) :
    ∀ (l : List γ), (∀ x ∈ l, ∀ acc, I acc → RunPost ctx (fun st => I st.value) (body x acc)) →
      ∀ init, I init → RunPost ctx I (forIn l init body)
  | [], _, init, h => by rw [List.forIn_nil]; exact RunPost.pure h
  | x :: l, hb, init, h => by
    rw [List.forIn_cons]
    refine RunPost.bind (hb x List.mem_cons_self init h) fun st hst => ?_
    cases st with
    | done b => exact RunPost.pure hst
    | yield b =>
      exact RunPost.forIn ctx I body l (fun y hy => hb y (List.mem_cons_of_mem _ hy)) b hst

/-- The constructors `MutConst.mkIndc` collects are stored, as constructors,
under names of the list. -/
theorem collectCtors_post (ctx : CompileEnv × BlockEnv) (L : List Name) :
    ∀ (names : List Name) (acc : Array ConstructorVal),
      (∀ ctor ∈ acc, ∃ c ∈ L, ctx.1.env.get? c = some (.ctorInfo ctor)) → (∀ c ∈ names, c ∈ L) →
      RunPost ctx (fun out => ∀ ctor ∈ out, ∃ c ∈ L, ctx.1.env.get? c = some (.ctorInfo ctor))
        (collectMutConstConstructors names acc)
  | [], acc, h, _ => by
    rw [collectMutConstConstructors]
    exact RunPost.pure h
  | c :: rest, acc, h, hn => by
    rw [collectMutConstConstructors]
    refine RunPost.bind (RunPost.findConst ctx c) fun ci hci => ?_
    split
    · refine collectCtors_post ctx L rest _ (fun ctor hctor => ?_) (fun c' hc' => hn c' (by simp [hc']))
      rcases Array.mem_push.1 hctor with hctor | rfl
      · exact h ctor hctor
      · exact ⟨c, hn c (by simp), hci⟩
    · exact RunPost.throw _

theorem mkIndc_post (ctx : CompileEnv × BlockEnv) (val : InductiveVal) :
    RunPost ctx (fun m => m.name = val.cnst.name ∧
        ∀ ctor ∈ m.ctors, ∃ c ∈ val.ctors.toList, ctx.1.env.get? c = some (.ctorInfo ctor))
      (MutConst.mkIndc val) := by
  unfold MutConst.mkIndc
  exact RunPost.bind (collectCtors_post ctx val.ctors.toList _ #[] (by simp) fun _ h => h)
    fun ctors h => RunPost.pure ⟨rfl, h⟩

/-- A mutual source the block compile reads: the constant stored under a
member's name, with that constant's name, and, for an inductive, the
constructors stored under the names it lists. -/
def Member (E : Ix.Environment) (all : Ix.Set Name) (m : MutConst) : Prop :=
  ∃ n ci, all.contains n = true ∧ E.get? n = some ci ∧ m.name = ci.getCnst.name ∧
    ∀ ctor ∈ m.ctors, ∃ iv c, ci = .inductInfo iv ∧ c ∈ iv.ctors ∧ E.get? c = some (.ctorInfo ctor)

/-- **The block compile's members loop reads members**. -/
theorem members_post (ctx : CompileEnv × BlockEnv) (all : Ix.Set Name) :
    RunPost ctx (fun cs : Array MutConst => ∀ m ∈ cs, Member ctx.1.env all m)
      (forIn all #[] fun n (acc : Array Ix.MutConst) => do
        match ← findConst n with
        | .inductInfo val => pure (ForInStep.yield (acc.push (← MutConst.mkIndc val)))
        | .defnInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromDefinitionVal val)))
        | .opaqueInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromOpaqueVal val)))
        | .thmInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.fromTheoremVal val)))
        | .recInfo val => pure (ForInStep.yield (acc.push (Ix.MutConst.recr val)))
        | _ => pure (ForInStep.yield acc)) := by
  rw [Std.HashSet.forIn_eq_forIn_toList]
  refine RunPost.forIn ctx _ _ all.toList (fun n hn acc hacc => ?_) #[] (by simp)
  have hin : all.contains n = true :=
    Std.HashSet.mem_iff_contains.1 (Std.HashSet.mem_of_mem_toList hn)
  have push : ∀ m, Member ctx.1.env all m → ∀ m' ∈ acc.push m, Member ctx.1.env all m' := by
    intro m hm m' hm'
    rcases Array.mem_push.1 hm' with hm' | rfl
    · exact hacc m' hm'
    · exact hm
  refine RunPost.bind (RunPost.findConst ctx n) fun ci hci => ?_
  split
  · rename_i val
    refine RunPost.bind (mkIndc_post ctx val) fun m hm => RunPost.pure (push m ?_)
    refine ⟨n, _, hin, hci, hm.1, fun ctor hctor => ?_⟩
    obtain ⟨c, hc, hcs⟩ := hm.2 ctor hctor
    exact ⟨val, c, rfl, Array.mem_toList_iff.1 hc, hcs⟩
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.fromDefinitionVal, Ix.MutConst.ctors])⟩)
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.fromOpaqueVal, Ix.MutConst.ctors])⟩)
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.fromTheoremVal, Ix.MutConst.ctors])⟩)
  · exact RunPost.pure (push _ ⟨n, _, hin, hci, rfl, fun ctor h => absurd h (by
      simp [Ix.MutConst.ctors])⟩)
  · exact RunPost.pure hacc

/-- `x` is the name of a member the block compile reads, or of a constructor
such a member lists. -/
def MemberName (E : Ix.Environment) (all : Ix.Set Name) (x : Name) : Prop :=
  ∃ m, Member E all m ∧ (x = m.name ∨ ∃ ctor ∈ m.ctors, x = ctor.cnst.name)

/-- **Lean's order only arranges a block's members**: every class
`sourceClasses` returns holds members of its input. -/
theorem mem_sourceClasses {cs : Array MutConst} {c : List MutConst} {x : MutConst}
    (hc : c ∈ sourceClasses cs) (hx : x ∈ c) : x ∈ cs := by
  unfold sourceClasses at hc
  try dsimp only at hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  have hx : x = e.1 := List.mem_singleton.1 hx
  subst hx
  exact Array.fst_mem_of_mem_zipIdx (Ix.CompileCert.Canon.mem_qsort.1 (Array.mem_toList_iff.1 he))

/-- **The block compile's projections carry members' names**: a lone
constant's compile has none (`constantInfo_lone`), and the mutual compile's
are its sources' (`mutualBlock_names`), which Lean's order only arranges
(`mem_sourceClasses`) and which the members loop reads (`members_post`). -/
theorem compileBlockWithAux_names {ctx : CompileEnv × BlockEnv} {lo : Name} {all : Ix.Set Name}
    {s s' : BlockState} {r : BlockResult} {layout? : Option Ixon.AuxLayout}
    (h : rawRun (compileBlockWithAux lo all) ctx s = (.ok (r, layout?), s')) :
    ∀ row ∈ r.projections, MemberName ctx.1.env all row.1 := by
  unfold compileBlockWithAux at h
  obtain ⟨const, s₁, hc, h⟩ := bind_ok h
  dsimp only at h
  -- the kind test, then the lone test
  split at h <;> split at h
  all_goals first
    | (rename_i hcond; simp at hcond; done)
    | (obtain ⟨result, s₂, hr, h⟩ := bind_ok h
       have none := constantInfo_lone _ (by assumption) (by assumption)
         ctx s₁ result s₂ hr
       rw [rawRun_pure] at h
       cases h
       intro row hrow
       rw [none] at hrow
       exact absurd hrow (by simp))
    | (obtain ⟨cs, s₂, hcs, h⟩ := bind_ok h
       obtain ⟨out, s₄, hout, h⟩ := bind_ok h
       have same : Ix.Cert.BlockRecords.recordsOf r = Ix.Cert.BlockRecords.recordsOf out := by
         revert h
         refine Ix.Cert.BlockRecords.Returns.elim
           (P := fun (x : BlockResult × Option Ixon.AuxLayout) =>
             Ix.Cert.BlockRecords.recordsOf x.1 = Ix.Cert.BlockRecords.recordsOf out) ?_
         repeat returns_step
       have members := members_post ctx all s₁ cs s₂ hcs
       have names := mutualBlock_names (sourceClasses cs) ctx s₂ out s₄ hout
       intro row hrow
       unfold Ix.Cert.BlockRecords.recordsOf at same
       have hmap : (row.1, row.2.1) ∈ out.projections.map (fun p => (p.1, p.2.1)) := by
         rw [← (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj same).2).2).2]
         exact Array.mem_map_of_mem hrow
       obtain ⟨row', hrow', he⟩ := Array.mem_map.1 hmap
       obtain ⟨src, ⟨c, hc', hsrc⟩, hname⟩ := names row' hrow'
       have hm := members src (mem_sourceClasses hc' hsrc)
       rw [← (Prod.mk.inj he).1]
       exact ⟨src, hm, hname⟩)

end members

/-! ## The claims of a block compile -/

section claims

/-- `ci'` keeps `ci`'s name and, for an inductive, its constructors. -/
def Keeps (ci ci' : ConstantInfo) : Prop :=
  ci'.getCnst.name = ci.getCnst.name ∧
    ∀ iv', ci' = .inductInfo iv' → ∃ iv, ci = .inductInfo iv ∧ iv'.ctors = iv.ctors

/-- `E'` holds, under each name, a constant that keeps the name and constructors
of a constant `E` holds under a `==` name. -/
def Agrees (E E' : Ix.Environment) : Prop :=
  ∀ x ci', E'.get? x = some ci' → ∃ n ci, (n == x) = true ∧ E.get? n = some ci ∧ Keeps ci ci'

theorem Agrees.refl (E : Ix.Environment) : Agrees E E :=
  fun x ci h => ⟨x, ci, BEq.rfl, h, rfl, fun iv' h' => ⟨iv', h', rfl⟩⟩

/-- Every constant `E` holds carries a name `==` the one it is held under. -/
def NamedEnv (E : Ix.Environment) : Prop :=
  ∀ x ci, E.get? x = some ci → (ci.getCnst.name == x) = true

theorem Agrees.named {E E' : Ix.Environment} (ha : Agrees E E') (hn : NamedEnv E) : NamedEnv E' := by
  intro x ci' h
  obtain ⟨n, ci, hnx, hci, keeps⟩ := ha x ci' h
  rw [keeps.1]
  exact PartialEquivBEq.trans (hn n ci hci) hnx

/-- `x` hashes like a member of `all`, or like a constructor an inductive
member lists in `E`. -/
def Owned (E : Ix.Environment) (all : Ix.Set Name) (x : Name) : Prop :=
  (∃ m, all.contains m = true ∧ (x == m) = true) ∨
    ∃ I iv c, all.contains I = true ∧ E.get? I = some (.inductInfo iv) ∧ c ∈ iv.ctors ∧ (x == c) = true

theorem memberName_owned {E E' : Ix.Environment} {all : Ix.Set Name} {x : Name} (ha : Agrees E E')
    (hn : NamedEnv E) (h : MemberName E' all x) : Owned E all x := by
  have hn' := ha.named hn
  obtain ⟨m, ⟨n, ci', hin, hci', hname, hctors⟩, hx⟩ := h
  rcases hx with rfl | ⟨ctor, hctor, rfl⟩
  · exact .inl ⟨n, hin, by rw [hname]; exact hn' n ci' hci'⟩
  · obtain ⟨iv', c, rfl, hc, hcs⟩ := hctors ctor hctor
    obtain ⟨n₀, ci₀, hn₀, hci₀, -, kind⟩ := ha n _ hci'
    obtain ⟨iv₀, rfl, same⟩ := kind iv' rfl
    refine .inr ⟨n₀, iv₀, c, ?_, hci₀, same ▸ hc, hn' c _ hcs⟩
    rw [Std.HashSet.contains_congr hn₀]
    exact hin

/-- **The claims of a block compile**: every projection name of
`runBlockWithAux cenv all lo` hashes like a member of `all` or like a
constructor an inductive member lists, when every constant of the environment
carries its name (`compileBlockWithAux_names`). -/
theorem runBlockWithAux_owned {cenv : CompileEnv} {all : Ix.Set Name} {lo : Name} {r : BlockResult}
    {cache : BlockState} {layout? : Option Ixon.AuxLayout}
    (hn : NamedEnv cenv.env) (h : runBlockWithAux cenv all lo = .ok (r, cache, layout?)) :
    ∀ row ∈ r.projections, Owned cenv.env all row.1 := by
  unfold runBlockWithAux at h
  obtain ⟨⟨⟨result, layout'⟩, cache'⟩, hrun, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  try dsimp only at h
  have hr : r = result := by
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  subst hr
  have names := compileBlockWithAux_names (Ix.CompileCert.run_success hrun)
  intro row hrow
  exact memberName_owned (Agrees.refl _) hn (names row hrow)

end claims

/-- **The claims of a block compile**: every projection name of
`runBlock cenv all lo` hashes like a member of `all` or like a constructor an
inductive member lists, when every constant of `cenv.env` carries its name
(`runBlockWithAux_owned`). -/
theorem runBlock_owned {cenv : CompileEnv} {all : Ix.Set Name} {lo : Name} {r : BlockResult}
    {cache : BlockState} {layout? : Option Ixon.AuxLayout}
    (hn : NamedEnv cenv.env) (h : runBlock cenv all lo = .ok (r, cache, layout?)) :
    ∀ row ∈ r.projections, Owned cenv.env all row.1 :=
  runBlockWithAux_owned hn h

end Ix.Cert.Claims
