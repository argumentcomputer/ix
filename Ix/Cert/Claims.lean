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
  matter, so no hypothesis on the names (`Canon.KeysDistinct`) is needed;
* a mutual block's projections carry its members' names and their
  constructors' (`mutualBlock_names`), and a lone constant other than an
  inductive or a constructor has none (`constantInfo_lone`);
* whatever Pass 3's hooks return, `runBlockWithAux`'s projections carry those
  names (`runBlockWithAux_owned`), and an image block's result, the image of
  its key, has none (`runImageBlock_lone`), so every claim of `runBlock` is
  owned or the key (`runBlock_owned`). -/

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
  fun _ _ _ hr => Ix.Cert.PassHooks.findConst_ok hr

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

/-- **The block compile's projections carry members' names**: a lone
constant's compile has none (`constantInfo_lone`), and the mutual compile's
are its sources' (`mutualBlock_names`), which the sort and the recursor
order only regroup (`sortClasses_mem`, `orderRecursorFamily_perm`) and which
the members loop reads (`members_post`). -/
theorem compileBlockWithAux_names {ctx : CompileEnv × BlockEnv} {lo : Name} {all : Ix.Set Name}
    {s s' : BlockState} {r : BlockResult} {layout? : Option Ixon.AuxLayout}
    {pub : Ix.Compile.Pass.Published}
    (h : rawRun (compileBlockWithAux lo all) ctx s = (.ok (r, layout?, pub), s')) :
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
       obtain ⟨sorted, s₃, hsorted, h⟩ := bind_ok h
       obtain ⟨out, s₄, hout, h⟩ := bind_ok h
       have same : Ix.Cert.PassHooks.recordsOf r = Ix.Cert.PassHooks.recordsOf out := by
         revert h
         refine Ix.Cert.PassHooks.Returns.elim
           (P := fun (x : BlockResult × Option Ixon.AuxLayout × Ix.Compile.Pass.Published) =>
             Ix.Cert.PassHooks.recordsOf x.1 = Ix.Cert.PassHooks.recordsOf out) ?_
         repeat returns_step
       have members := members_post ctx all s₁ cs s₂ hcs
       obtain ⟨-, addresses, stats, sortedRun⟩ := Ix.CompileCert.ProjectionLayout.sort_run cs.toList hsorted
       have regrouped := sortClasses_mem sortedRun
       have names := mutualBlock_names (orderRecursorFamily sorted) ctx s₃ out s₄ hout
       intro row hrow
       unfold Ix.Cert.PassHooks.recordsOf at same
       have hmap : (row.1, row.2.1) ∈ out.projections.map (fun p => (p.1, p.2.1)) := by
         rw [← (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj same).2).2).2]
         exact Array.mem_map_of_mem hrow
       obtain ⟨row', hrow', he⟩ := Array.mem_map.1 hmap
       obtain ⟨src, ⟨c, hc', hsrc⟩, hname⟩ := names row' hrow'
       have hc'' := (Ix.CompileCert.MutualArtifact.orderRecursorFamily_perm sorted).mem_iff.1 hc'
       have hm := members src (Array.mem_toList_iff.1 (regrouped c hc'' src hsrc))
       rw [← (Prod.mk.inj he).1]
       exact ⟨src, hm, hname⟩)

end members

/-! ## Pass 3's rewrite keeps names -/

section rewrite

open Ix.Compile.Pass (RwM RwConfig RwState)

variable {α β : Type}

/-- Every successful rewrite run returns a value satisfying `P`. -/
def RwPost (P : α → Prop) (x : RwM α) : Prop :=
  ∀ cfg st v st', (x.run cfg).run st = .ok (v, st') → P v

theorem RwPost.pure {P : α → Prop} {a : α} (h : P a) : RwPost P (Pure.pure a : RwM α) := by
  intro cfg st v st' hr
  cases hr
  exact h

theorem RwPost.bind {x : RwM α} {f : α → RwM β} {q : α → Prop} {p : β → Prop}
    (hx : RwPost q x) (hf : ∀ a, q a → RwPost p (f a)) : RwPost p (x >>= f) := by
  intro cfg st v st' hr
  rw [ReaderT.run_bind, StateT.run_bind] at hr
  cases h : (x.run cfg).run st with
  | error e => rw [h] at hr; cases hr
  | ok r => rw [h] at hr; exact hf r.1 (hx cfg st r.1 r.2 h) cfg r.2 v st' hr

theorem RwPost.bindAny {x : RwM α} {f : α → RwM β} {p : β → Prop} (hf : ∀ a, RwPost p (f a)) :
    RwPost p (x >>= f) :=
  RwPost.bind (q := fun _ => True) (fun _ _ _ _ _ => trivial) fun a _ => hf a

theorem RwPost.ite {p : α → Prop} {c : Prop} [Decidable c] {a b : RwM α} (ha : RwPost p a)
    (hb : RwPost p b) : RwPost p (if c then a else b) := by
  by_cases hc : c
  · simpa [hc] using ha
  · simpa [hc] using hb

/-- The rewrite keeps a constant's name and an inductive's constructors. -/
def Keeps (ci ci' : ConstantInfo) : Prop :=
  ci'.getCnst.name = ci.getCnst.name ∧
    ∀ iv', ci' = .inductInfo iv' → ∃ iv, ci = .inductInfo iv ∧ iv'.ctors = iv.ctors

/-- **Pass 3's rewrite of a constant keeps its name and an inductive's
constructors**: it rewrites the terms only (`Ix.Compile.Pass.rewriteConstM`). -/
theorem rewriteConstM_keeps (expansion? : Name → Except String (Option Ix.Compile.Pass.Expansion))
    (ci : ConstantInfo) :
    RwPost (fun r => Keeps ci r.1) (Ix.Compile.Pass.rewriteConstM expansion? ci) := by
  have cnst : ∀ c : Ix.ConstantVal, RwPost (fun r : Ix.ConstantVal × Bool => r.1.name = c.name)
      (do let (t, ch) ← Ix.Compile.Pass.rw expansion? Ix.Compile.Pass.rewriteFuel true c.type
          pure ({ c with type := t }, ch)) := fun c =>
    RwPost.bindAny fun _ => RwPost.pure rfl
  unfold Ix.Compile.Pass.rewriteConstM
  cases ci <;>
  · refine RwPost.bind (cnst _) fun r hr => ?_
    repeat (first
      | (with_reducible apply RwPost.bindAny); intro _
      | (with_reducible apply RwPost.ite)
      | split)
    all_goals ((try dsimp only); exact RwPost.pure ⟨hr, fun iv' h => by
      first | (cases h; done) | (cases h; exact ⟨_, rfl, rfl⟩)⟩)


/-- **A block rewrite's overlay holds rewrites of its members**: each entry
is a member's name with the rewrite of that member's constant. -/
theorem rewriteBlock_overlay {expansion? : Name → Except String (Option Ix.Compile.Pass.Expansion)}
    {members : Array (Name × ConstantInfo)} {cfg : RwConfig} {rwr : Ix.Compile.Pass.BlockRewrite}
    (h : Ix.Compile.Pass.rewriteBlock expansion? members cfg = .ok rwr) :
    ∀ p ∈ rwr.overlay, ∃ ci, (p.1, ci) ∈ members ∧ Keeps ci p.2 := by
  unfold Ix.Compile.Pass.rewriteBlock at h
  obtain ⟨res, hloop, hret⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  have inv := Ix.CompileCert.Loop.forIn_inv_array
    (I := fun _ (s : RwState × Array (Name × ConstantInfo) × Array (Name × String)) =>
      ∀ p ∈ s.2.1, ∃ ci, (p.1, ci) ∈ members ∧ Keeps ci p.2) _ members ?_ (by simp) hloop
  · dsimp only at hret
    cases hret
    exact inv
  · intro pre x post s r hx hI hstep
    obtain ⟨n, ci⟩ := x
    dsimp only at hstep
    obtain ⟨⟨⟨ci', changed⟩, st'⟩, hrun, hstep⟩ := Ix.CompileCert.Loop.except_bind_ok.1 hstep
    have keeps : Keeps ci ci' := rewriteConstM_keeps expansion? ci cfg s.1 _ st' hrun
    have hmem : (n, ci) ∈ members := Array.mem_toList_iff.1 (by rw [← hx]; simp)
    dsimp only at hstep
    obtain ⟨decl, -, hstep⟩ := Ix.CompileCert.Loop.except_bind_ok.1 hstep
    split at hstep
    · cases hstep
      refine ⟨_, rfl, fun p hp => ?_⟩
      rcases Array.mem_push.1 hp with hp | rfl
      · exact hI p hp
      · exact ⟨ci, hmem, keeps⟩
    · cases hstep
      exact ⟨_, rfl, hI⟩


/-- `E'` holds, under each name, the rewrite of a constant `E` holds under a
`==` name. -/
def Agrees (E E' : Ix.Environment) : Prop :=
  ∀ x ci', E'.get? x = some ci' → ∃ n ci, (n == x) = true ∧ E.get? n = some ci ∧ Keeps ci ci'

theorem Agrees.refl (E : Ix.Environment) : Agrees E E :=
  fun x ci h => ⟨x, ci, BEq.rfl, h, rfl, fun iv' h' => ⟨iv', h', rfl⟩⟩

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {v : α} (h : x.mapError f = .ok v) :
    x = .ok v := by
  cases x with
  | error e => cases h
  | ok a => cases h; rfl

/-- A lookup in the overlay map finds an entry under a `==` name. -/
theorem overlay_get (L : List (Name × ConstantInfo)) :
    ∀ (l : List (Name × ConstantInfo)) (m : Std.HashMap Name ConstantInfo), (∀ y ∈ l, y ∈ L) →
      (∀ k v, m.get? k = some v → ∃ n, (n, v) ∈ L ∧ (n == k) = true) →
      ∀ k v, (l.foldl (fun m x => match x with | (n, ci) => m.insert n ci) m).get? k = some v →
        ∃ n, (n, v) ∈ L ∧ (n == k) = true
  | [], _, _, hm => hm
  | (yn, yci) :: l, m, hl, hm => by
    rw [List.foldl_cons]
    refine overlay_get L l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (fun k v h => ?_)
    rw [Std.HashMap.get?_insert] at h
    split at h
    · rename_i hy
      cases h
      exact ⟨yn, hl _ List.mem_cons_self, hy⟩
    · exact hm k v h

/-- **Hook 2 keeps the environment's names**: the environment `prepareBlock`
returns is its input's, or the input overlaid with rewrites of members'
constants (`rewriteBlock_overlay`). -/
theorem prepareBlock_agrees {cenv cenv' : CompileEnv} {all : Ix.Set Name} {lo : Name}
    {p : Ix.Compile.Pass.Published} (h : Ix.Compile.Pass.prepareBlock cenv all lo = .ok (cenv', p)) :
    Agrees cenv.env cenv'.env := by
  unfold Ix.Compile.Pass.prepareBlock at h
  repeat' (first
    | (cases h; exact Agrees.refl _)
    | (dsimp only at h; split at h)
    | split at h)
  all_goals
    obtain ⟨res, hloop, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
    have members : ∀ q ∈ res.1, cenv.env.get? q.1 = some q.2 := by
      rw [Std.HashSet.forIn_eq_forIn_toList] at hloop
      refine Ix.CompileCert.Loop.forIn_inv
        (I := fun _ (s : Array (Name × ConstantInfo) × Array Name) => ∀ q ∈ s.1, cenv.env.get? q.1 = some q.2)
        _ all.toList ?_ all.toList [] _ res rfl (by simp) hloop
      intro pre x post s r _ hI hstep
      try dsimp only at hstep
      split at hstep
      · rename_i ci hci
        obtain ⟨used', -, hstep⟩ := Ix.CompileCert.Loop.except_bind_ok.1 hstep
        cases hstep
        refine ⟨_, rfl, fun q hq => ?_⟩
        rcases Array.mem_push.1 hq with hq | rfl
        · exact hI q hq
        · exact hci
      · cases hstep
        exact ⟨_, rfl, hI⟩
    try dsimp only at h
    split at h
    · cases h
      exact Agrees.refl _
    · obtain ⟨views, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
      try dsimp only at h
      obtain ⟨rwr, hrw, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
      have overlay := rewriteBlock_overlay (mapError_ok hrw)
      split at h
      · cases h
        exact Agrees.refl _
      · try dsimp only at h
        cases h
        intro x ci' hx
        have e : (∅ : Std.HashMap Name ConstantInfo).get? x = none := by
          rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]
        rw [Ix.Environment.get?] at hx
        dsimp only at hx
        rw [e] at hx
        dsimp only at hx
        cases ho : (rwr.overlay.foldl (fun m x => match x with | (n, ci) => m.insert n ci)
            (∅ : Std.HashMap Name ConstantInfo)).get? x with
        | none =>
          rw [ho] at hx
          exact ⟨x, ci', BEq.rfl, hx, rfl, fun iv' h' => ⟨iv', h', rfl⟩⟩
        | some ci'' =>
          rw [ho] at hx
          cases hx
          rw [← Array.foldl_toList] at ho
          obtain ⟨n, hn, hnx⟩ := overlay_get rwr.overlay.toList rwr.overlay.toList ∅ (fun _ h => h)
            (fun k v h => by simp at h) x ci' ho
          obtain ⟨ci, hci, keeps⟩ := overlay (n, ci') (Array.mem_toList_iff.1 hn)
          exact ⟨n, ci, hnx, members (n, ci) hci, keeps⟩

end rewrite

/-! ## The claims of a block compile, hooks or not -/

section claims

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

/-- **The claims of a block compile, with Pass 3's hooks in any state**:
every projection name of `runBlockWithAux cenv all lo` hashes like a member
of `all` or like a constructor an inductive member lists, when every
constant of the environment carries its name (`prepareBlock_agrees`,
`compileBlockWithAux_names`). -/
theorem runBlockWithAux_owned {cenv : CompileEnv} {all : Ix.Set Name} {lo : Name} {r : BlockResult}
    {cache : BlockState} {layout? : Option Ixon.AuxLayout} {pub : Ix.Compile.Pass.Published}
    (hn : NamedEnv cenv.env) (h : runBlockWithAux cenv all lo = .ok (r, cache, layout?, pub)) :
    ∀ row ∈ r.projections, Owned cenv.env all row.1 := by
  unfold runBlockWithAux at h
  obtain ⟨⟨cenv', prepared⟩, hprep, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  try dsimp only at h
  obtain ⟨⟨⟨result, layout', published⟩, cache'⟩, hrun, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  try dsimp only at h
  have hr : r = Ix.Compile.Pass.withMetaRefs cache'.p3MetaRefs lo result := by
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  subst hr
  have names := compileBlockWithAux_names (Ix.CompileCert.run_success hrun)
  have same := (Ix.Cert.PassHooks.withMetaRefs_records cache'.p3MetaRefs lo result).1
  unfold Ix.Cert.PassHooks.recordsOf at same
  intro row hrow
  have hmap : (row.1, row.2.1) ∈ result.projections.map (fun p => (p.1, p.2.1)) := by
    rw [← (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj same).2).2).2]
    exact Array.mem_map_of_mem hrow
  obtain ⟨row', hrow', he⟩ := Array.mem_map.1 hmap
  rw [← (Prod.mk.inj he).1]
  exact memberName_owned (prepareBlock_agrees hprep) hn (names row' hrow')

end claims

/-! ## Image blocks claim their key only -/

section image

/-- A constant other than an inductive or a constructor (`constantInfo_lone`'s
premises). -/
def Lone (ci : ConstantInfo) : Prop :=
  (∀ v, ci = .inductInfo v → False) ∧ ∀ v, ci = .ctorInfo v → False

/-- An invariant of a fallible loop's state, kept by every step from a
member of the list, holds of its result (`done` or not). -/
theorem forIn_list_inv {α σ ε : Type} (I : σ → Prop) (f : α → σ → Except ε (ForInStep σ)) :
    ∀ (l : List α), (∀ x ∈ l, ∀ s r, I s → f x s = .ok r → I r.value) →
      ∀ (s res : σ), I s → forIn l s f = .ok res → I res := by
  intro l
  induction l with
  | nil => intro _ s res hs h; cases h; exact hs
  | cons x l ih =>
    intro step s res hs h
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
    have hv := step x List.mem_cons_self s r hs hr
    cases r with
    | done b => cases h; exact hv
    | yield b => exact ih (fun y hy => step y (List.mem_cons_of_mem _ hy)) b res hv h

/-- `forIn_list_inv` over an array. -/
theorem forIn_array_inv {α σ ε : Type} (I : σ → Prop) (f : α → σ → Except ε (ForInStep σ)) (xs : Array α)
    (step : ∀ x ∈ xs, ∀ s r, I s → f x s = .ok r → I r.value) {s res : σ} (hs : I s)
    (h : forIn xs s f = .ok res) : I res := by
  rw [← Array.forIn_toList] at h
  exact forIn_list_inv I f xs.toList (fun x hx => step x (Array.mem_toList_iff.1 hx)) s res hs h

/-- `forIn_list_inv` over a range `[:n]` (a bounded `for`, `break` included). -/
theorem forIn_range_inv {σ ε : Type} (I : σ → Prop) (f : Nat → σ → Except ε (ForInStep σ)) (n : Nat)
    (step : ∀ x s r, I s → f x s = .ok r → I r.value) {s res : σ} (hs : I s)
    (h : forIn [:n] s f = .ok res) : I res := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  exact forIn_list_inv I f _ (fun x _ => step x) s res hs h

/-- An image constant is a definition or a theorem. -/
theorem imageInfo_lone (cenv : CompileEnv) (dv : Ix.DefinitionVal) :
    Lone (Ix.Compile.Pass.imageInfo cenv dv) := by
  unfold Ix.Compile.Pass.imageInfo
  constructor <;> intro v h <;> split at h <;> cases h

/-- An image compiles alone, to no projections. -/
theorem compileImage_lone {cenv : CompileEnv} {known : Std.HashMap Ix.Compile.ExactKey.ExactName Address}
    {ci : ConstantInfo} {r : BlockResult} {bs : BlockState} (hk : Lone ci)
    (h : Ix.Compile.Pass.compileImage cenv known ci = .ok (r, bs)) : r.projections = #[] := by
  unfold Ix.Compile.Pass.compileImage at h
  dsimp only at h
  split at h
  · rename_i r' heq
    cases h
    exact constantInfo_lone ci hk.1 hk.2 _ _ _ _ (Ix.CompileCert.run_success heq)
  · cases h

/-- **An image block's images have no projections**: each is `compileImage` of
an `imageInfo` (a definition or a theorem, `constantInfo_lone`), through the
declarations loop and the bounded rounds of `compileImageBlock`. -/
theorem compileImageBlock_lone {cenv : CompileEnv} {all : Ix.Set Name}
    {imgs : Array (Name × BlockResult × BlockState)} {pub : Ix.Compile.Pass.Published}
    (h : Ix.Compile.Pass.compileImageBlock cenv all = .ok (imgs, pub)) :
    ∀ x ∈ imgs, x.2.1.projections = #[] := by
  unfold Ix.Compile.Pass.compileImageBlock at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  obtain ⟨views, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  obtain ⟨s2, h2, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  have hd : ∀ p ∈ s2.2.1, Lone p.2 := by
    refine forIn_array_inv (fun s : Ix.Compile.Pass.RwState × Array (Name × ConstantInfo) ×
      Array (Name × Ix.Compile.Pass.Expansion × Expr) => ∀ p ∈ s.2.1, Lone p.2) _ _ ?_
      (fun _ hp => by simp at hp) h2
    intro a _ s r hs hr
    repeat' (first
      | (obtain ⟨_, _, hr⟩ := Ix.CompileCert.Loop.except_bind_ok.1 hr)
      | (split at hr))
    all_goals first
      | (cases hr; done)
      | (cases hr; exact hs)
      | (cases hr
         intro p hp
         rcases Array.mem_push.1 hp with hp | rfl
         exacts [hs p hp, imageInfo_lone _ _])
  obtain ⟨s3, h3, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  have ho : (∀ p ∈ s3.1, Lone p.2) ∧ ∀ x ∈ s3.2.2.1, x.2.1.projections = #[] := by
    refine forIn_range_inv (fun s : Array (Name × ConstantInfo) × Std.HashMap Ix.Compile.ExactKey.ExactName Address ×
      Array (Name × BlockResult × BlockState) × String =>
        (∀ p ∈ s.1, Lone p.2) ∧ ∀ x ∈ s.2.2.1, x.2.1.projections = #[]) _ _ ?_
      ⟨hd, fun _ hx => by simp at hx⟩ h3
    intro _ s r hs hr
    split at hr
    · cases hr; exact hs
    · obtain ⟨t, ht, hr⟩ := Ix.CompileCert.Loop.except_bind_ok.1 hr
      cases hr
      refine forIn_array_inv (fun t : Std.HashMap Ix.Compile.ExactKey.ExactName Address ×
        Array (Name × BlockResult × BlockState) × String × Array (Name × ConstantInfo) =>
          (∀ x ∈ t.2.1, x.2.1.projections = #[]) ∧ ∀ p ∈ t.2.2.2, Lone p.2) _ _ ?_
        ⟨hs.2, fun _ hp => by simp at hp⟩ ht |>.symm
      intro x hx u q hu hq
      split at hq
      · rename_i r bs hc
        cases hq
        refine ⟨fun y hy => ?_, hu.2⟩
        rcases Array.mem_push.1 hy with hy | rfl
        exacts [hu.1 y hy, compileImage_lone (hs.1 x hx) hc]
      · cases hq
        refine ⟨hu.1, fun y hy => ?_⟩
        rcases Array.mem_push.1 hy with hy | rfl
        exacts [hu.2 y hy, hs.1 _ hx]
  split at h
  · obtain ⟨_, h, -⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
    cases h
  · cases h
    exact ho.2

/-- An image block's result, the image of its key, has no projections. -/
theorem runImageBlock_lone
    {original : CompileEnv → Name → Ix.Set Name → Except CompileError (BlockResult × BlockState)}
    {cenv : CompileEnv} {all : Ix.Set Name} {lo : Name} {r : BlockResult} {cache : BlockState}
    {pub : Ix.Compile.Pass.Published}
    (h : Ix.Compile.Pass.runImageBlock original cenv all lo = .ok (r, cache, pub)) : r.projections = #[] := by
  unfold Ix.Compile.Pass.runImageBlock at h
  dsimp only at h
  obtain ⟨⟨imgs, published⟩, himgs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  have lone := compileImageBlock_lone (mapError_ok himgs)
  obtain ⟨_, -, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h
  obtain ⟨s, hs, h⟩ := Ix.CompileCert.Loop.except_bind_ok.1 h

  have hr : ∀ q, s.2 = some q → q.projections = #[] := by
    refine forIn_array_inv (fun s : BlockState × Option BlockResult => ∀ q, s.2 = some q → q.projections = #[])
      _ _ ?_ (fun _ hq => by cases hq) hs
    intro x hx u v hu hv
    split at hv
    · cases hv
      intro q hq
      cases hq
      exact lone x hx
    · cases hv
      exact hu
  split at h
  · rename_i q hq
    cases h
    exact hr _ hq
  · cases h

/-- **The claims of a block compile, image blocks included**: every projection
name of `runBlock cenv all lo` hashes like a member of `all` or like a
constructor an inductive member lists, when every constant of `cenv.env`
carries its name (`runBlockWithAux_owned`; an image block's result has none,
`runImageBlock_lone`, so its only claim is its key). -/
theorem runBlock_owned {cenv : CompileEnv} {all : Ix.Set Name} {lo : Name} {r : BlockResult}
    {cache : BlockState} {layout? : Option Ixon.AuxLayout} {pub : Ix.Compile.Pass.Published}
    (hn : NamedEnv cenv.env) (h : runBlock cenv all lo = .ok (r, cache, layout?, pub)) :
    ∀ row ∈ r.projections, Owned cenv.env all row.1 := by
  unfold runBlock at h
  split at h
  · cases hi : Ix.Compile.Pass.runImageBlock compileConstNoAuxPure cenv all lo with
    | error e => rw [hi] at h; cases h
    | ok v =>
      rw [hi] at h
      cases h
      rw [runImageBlock_lone hi]
      intro _ hrow
      simp at hrow
  · exact runBlockWithAux_owned hn h

end image

end Ix.Cert.Claims
