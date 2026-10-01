module

public import ConLeche.Cached.ParsedC
public import ConLeche.Verify.Cached.OpsC
public import ConLeche.Verify.EnvBound

public section

/-!
# The cached representation's guard walks and the conversion boundary

Task #163, batch 4.  The pieces of the cached clone that sit *between*
the parse arena and the core:

* the fabrication leaf guard (`fvarLeaves`/`leafMem`/`leavesSubC`/
  `leafGuard`) — the transposition of `leafGuard_spec'`
  (`ConLeche/Verify/IExprOps.lean`);
* the level-parameter definedness walk
  (`Expr.allLevelParamsDefined`) — the transposition of
  `allLevelParamsDefinedI_spec`;
* the constant-resolution walk (`constsResolveFC`) — the transposition
  of `constsResolveFI_spec`;
* the arena→`Expr` conversion (`ofStoreGo`/`ofStore`), the clone's
  counterpart of `EStore.readbackGo`: on a well-formed parse arena the
  conversion of a denoting index succeeds and yields a term whose
  erasure *is* the denotation.

Two structural differences from the arena twins are paid for here.

1. The clone's `fvarLeaves` walk carries a **`seen` set** (the arena's
   is a result memo), so the leaf *list* it returns is deduplicated and
   is **not** `Expr.fvarLeaves` of the erasure — only its *set of
   elements* is.  Since the only consumer (`leafMem`) is a membership
   test, a membership characterization is exactly what is needed, and
   `leafGuard_spec` still lands on `leafGuard_spec'`'s `Expr`-side
   right-hand side verbatim.

   Marking a node *before* descending into it is what makes the `seen`
   invariant ("a marked node's leaves are already in the accumulator")
   momentarily false for the node being processed and for its
   ancestors.  The proof closes that gap the way a DFS on an acyclic
   graph does: the invariant is relaxed by a *gray* predicate `G` on
   erasures ("…*or* the marked node is gray"), the call at `e` requires
   every gray erasure to be strictly bigger than `e` — which is
   what rules a hit at `e` itself out — and the call's post-condition
   pops `e` off `G` again, because by then `e`'s leaves *are* in
   the accumulator.  Acyclicity is free here: `Expr` is an inductive
   *tree*, so the size side-condition is discharged by each
   constructor's own `sizeF` recurrence.

2. `ofStoreGo` has `emlt` guards on every child (they make the
   traversal's `(etier, epos)` measure decrease without an arena
   hypothesis).  On a `TWF` store the children of a denoting node are
   `emlt`-below it (`denoteT_some_inv`), so no guard ever fires — the
   same discharge `readbackGo_spec` performs.
-/

namespace ConLeche.Expr

/-! ## Level-parameter definedness

`allLevelParamsDefinedC` is the pointer-keyed walk of
`ConLeche/Cached/ExprOpsC.lean` with the `hasLP` cutoff.  The walk
carries its own proof against the plain descent
`allLevelParamsDefinedP`, so all that is proved here is that plain
descent (and the cutoff arm, by `hasLP_eq _` plus
`Expr.allLevelParamsDefined_of_not_hasLevelParam`); there is no memo
invariant, because each entry carries its own proof. -/

/-- The walk's cutoff, read as the specification: a node without a
level parameter has all of them defined. -/
private theorem lpdP_cut_spec {ps : List Name} {e : Expr} (h : ¬ e.hasLP = true) :
    true = Expr.allLevelParamsDefined ps e :=
  (Expr.allLevelParamsDefined_of_not_hasLevelParam (params := ps)
    (by rw [← hasLP_eq _]; simpa using h)).symm

/-- **The plain descent is `Expr.allLevelParamsDefined`.** -/
theorem allLevelParamsDefinedP_spec {ps : List Name} : ∀ {e : Expr},
    Expr.allLevelParamsDefinedP ps e = Expr.allLevelParamsDefined ps e := by
  intro e
  induction e with
  | bvar i =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | lit l =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | sort u =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | const n us =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | fvar idx ty iht =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [iht, Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | app f a ihf iha =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [ihf, iha, Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | lam ty bd m iht ihb =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [iht, ihb, Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | forallE ty bd m iht ihb =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [iht, ihb, Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | letE ty val bd iht ihv ihb =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [iht, ihv, ihb, Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h
  | proj s i sub ihe =>
    rw [Expr.allLevelParamsDefinedP.eq_def]
    split
    · simp only [ihe, Expr.allLevelParamsDefined]
    · next h => exact lpdP_cut_spec h

/-- **`Expr.allLevelParamsDefined` is `Expr.allLevelParamsDefined` of
the erasure.** -/
theorem allLevelParamsDefinedC_spec {ps : List Name} {e : Expr} :
    Expr.allLevelParamsDefinedC ps e = (Expr.allLevelParamsDefined ps e) := by
  rw [Expr.allLevelParamsDefinedC.eq_def]
  split
  · rw [Expr.resBool_eq]; exact allLevelParamsDefinedP_spec
  · next h => exact lpdP_cut_spec h

/-! ## The fabrication leaf guard

`Expr.fvarLeaves` recurses into `fvar` annotations, so it is
well-founded on `sizeF` rather than structural: its per-constructor
equations have to be named before anything can rewrite with them. -/

private theorem fvarLeaves_bvar (i : Nat) :
    (Expr.bvar i).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_sort (u : Level) :
    (Expr.sort u).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_const (n : Name) (us : List Level) :
    (Expr.const n us).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_lit (l : Literal) :
    (Expr.lit l).fvarLeaves = [] := by simp [Expr.fvarLeaves]

private theorem fvarLeaves_fvar (idx : Nat) (ty : Expr) :
    (Expr.fvar idx ty).fvarLeaves = (idx, ty) :: ty.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_app (f a : Expr) :
    (Expr.app f a).fvarLeaves = f.fvarLeaves ++ a.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_lam (ty b : Expr) (m : BinderMeta) :
    (Expr.lam ty b m).fvarLeaves = ty.fvarLeaves ++ b.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_forallE (ty b : Expr) (m : BinderMeta) :
    (Expr.forallE ty b m).fvarLeaves = ty.fvarLeaves ++ b.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_letE (ty v b : Expr) :
    (Expr.letE ty v b).fvarLeaves
      = ty.fvarLeaves ++ v.fvarLeaves ++ b.fvarLeaves := by
  rw [Expr.fvarLeaves]

private theorem fvarLeaves_proj (s : Name) (i : Nat) (e : Expr) :
    (Expr.proj s i e).fvarLeaves = e.fvarLeaves := by rw [Expr.fvarLeaves]

/-- The clone's `fvarB == 0` shortcut on the leaf walks: a node whose
cached fvar range is zero has no `fvar` node outside annotations at
all, hence no reachable leaf (the counterpart of
`fvarLeaves_eq_nil_of_not_hasFvar` at the *range* cutoff). -/
private theorem fvarLeaves_nil_of_fvarsBelow_zero : ∀ (e : Expr),
    Expr.fvarsBelow 0 e → e.fvarLeaves = [] := by
  intro e
  induction e <;> intro hb <;>
    simp_all [Expr.fvarsBelow, fvarLeaves_bvar, fvarLeaves_sort,
      fvarLeaves_const, fvarLeaves_lit, fvarLeaves_app,
      fvarLeaves_lam, fvarLeaves_forallE, fvarLeaves_letE, fvarLeaves_proj]

/-- Erasure of a cached leaf list (the counterpart of the arena's
`leavesDen`; the annotation component goes through `eraseC`). -/
@[expose] def leavesEr (xs : List (Nat × Expr)) : List (Nat × Expr) :=
  xs.map fun l => (l.1, l.2)

@[simp] theorem leavesEr_nil : leavesEr [] = [] := rfl

@[simp] theorem leavesEr_cons (idx : Nat) (ty : Expr)
    (xs : List (Nat × Expr)) :
    leavesEr ((idx, ty) :: xs) = (idx, (ty : Expr)) :: leavesEr xs := rfl

/-! ### The `seen`-set walk

`fvarLeavesGo` marks a node **before** descending into it, so the
obvious invariant ("a marked node's leaves are already in the
accumulator") is false for the node currently being processed and for
its ancestors.  The invariant is therefore relaxed by a *gray*
predicate `G` on erasures, and the call at `e` requires every gray
erasure to be strictly bigger than `e` — which is what rules a
hit at `e` itself out.  Descending pushes `e` into `G`; the
call's post-condition pops it again, because by then `e`'s leaves *are*
in the accumulator.  `Expr` is an inductive tree, so the size
condition is discharged by the constructor's own `sizeF`
recurrence. -/

/-- The leaf walk's `seen`-set invariant at a gray predicate `G`. -/
@[expose] def SeenInv (G : Expr → Prop) (acc : List (Nat × Expr))
    (seen : Std.HashMap Expr Unit) : Prop :=
  ∀ (k : Expr) (u : Unit), seen[k]? = some u →
    (∀ l ∈ (Expr.fvarLeaves k), l ∈ leavesEr acc) ∨ G k

theorem SeenInv.empty {G : Expr → Prop}
    {acc : List (Nat × Expr)} : SeenInv G acc {} := by
  intro k u h
  simp at h

/-- Weakening: a bigger accumulator and a bigger gray predicate keep
the invariant. -/
theorem SeenInv.mono {G G' : Expr → Prop} {acc acc' : List (Nat × Expr)}
    {seen : Std.HashMap Expr Unit} (h : SeenInv G acc seen)
    (hacc : ∀ l, l ∈ leavesEr acc → l ∈ leavesEr acc')
    (hG : ∀ y, G y → G' y) : SeenInv G' acc' seen := by
  intro k u hk
  rcases h k u hk with hsub | hgray
  · exact Or.inl fun l hl => hacc l (hsub l hl)
  · exact Or.inr (hG _ hgray)

/-- Marking the node about to be descended into: it joins the gray
predicate. -/
theorem SeenInv.insertGray {G : Expr → Prop}
    {acc : List (Nat × Expr)} {seen : Std.HashMap Expr Unit}
    (h : SeenInv G acc seen) (e : Expr) :
    SeenInv (fun y => G y ∨ y = e) acc (seen.insert e ()) := by
  intro k u hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    exact Or.inr (Or.inr (beq_sound hbeq).symm)
  · rcases h k u hk with hsub | hgray
    · exact Or.inl hsub
    · exact Or.inr (Or.inl hgray)

/-- …and, once the descent is finished and the node's leaves are in the
accumulator, it leaves it again. -/
theorem SeenInv.dropGray {G : Expr → Prop}
    {acc : List (Nat × Expr)} {seen : Std.HashMap Expr Unit}
    {e : Expr} (h : SeenInv (fun y => G y ∨ y = e) acc seen)
    (he : ∀ l ∈ (Expr.fvarLeaves e), l ∈ leavesEr acc) :
    SeenInv G acc seen := by
  intro k u hk
  rcases h k u hk with hsub | hgray
  · exact Or.inl hsub
  · rcases hgray with hg | heq
    · exact Or.inr hg
    · exact Or.inl (by rw [heq]; exact he)

/-- **The leaf walk accumulates exactly the erasure's leaves** (as a
*set*: the `seen` dedup makes the list itself smaller than
`Expr.fvarLeaves`), keeps every annotation field-correct, and restores
the `seen` invariant at the caller's gray predicate. -/
theorem fvarLeavesGoC_spec : ∀ {e : Expr},
    ∀ {G : Expr → Prop} {acc : List (Nat × Expr)}
      {seen : Std.HashMap Expr Unit},
      SeenInv G acc seen →
      (∀ y, G y → e.sizeF < y.sizeF) →
      (∀ l, l ∈ leavesEr (Expr.fvarLeavesGoC acc seen e).1 ↔
          l ∈ leavesEr acc ∨ l ∈ (Expr.fvarLeaves e)) ∧
        SeenInv G (Expr.fvarLeavesGoC acc seen e).1 (Expr.fvarLeavesGoC acc seen e).2 := by
  intro e
  induction e with
  | bvar i =>
    intro G acc seen hseen hG
    rw [Expr.fvarLeavesGoC.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.bvar i)) = [] :=
      fvarLeaves_bvar i
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i u hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | sort u =>
    intro G acc seen hseen hG
    rw [Expr.fvarLeavesGoC.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.sort u)) = [] :=
      fvarLeaves_sort u
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | const n us =>
    intro G acc seen hseen hG
    rw [Expr.fvarLeavesGoC.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.const n us)) = [] :=
      fvarLeaves_const n us
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | lit l =>
    intro G acc seen hseen hG
    rw [Expr.fvarLeavesGoC.eq_def]
    have hnil : (Expr.fvarLeaves (Expr.lit l)) = [] :=
      fvarLeaves_lit l
    split
    · exact ⟨by simp [hnil], hseen⟩
    · split
      · rename_i v hhit
        exact ⟨by simp [hnil], hseen⟩
      · exact ⟨by simp [hnil],
          (hseen.insertGray _).dropGray (by simp [hnil])⟩
  | fvar idx ty iht =>
    intro G acc seen hseen hG
    have herase : (Expr.fvar idx ty)
        = Expr.fvar idx ty := rfl
    have hlv : (Expr.fvarLeaves (Expr.fvar idx ty))
        = (idx, ty) :: (Expr.fvarLeaves ty) := by
      rw [herase, fvarLeaves_fvar]
    rw [Expr.fvarLeavesGoC.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.fvar idx ty)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGty : ∀ y, (G y ∨ y = (Expr.fvar idx ty)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          have hs : (Expr.fvar idx ty).sizeF
              = ty.sizeF + 1 := by rw [herase]; rfl
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht
          ((hseen.insertGray _).mono
            (fun l h => by rw [leavesEr_cons]; exact List.mem_cons_of_mem _ h)
            (fun _ h => h))
          hGty
        rcases hp : Expr.fvarLeavesGoC ((idx, ty) :: acc) (seen.insert _ ()) ty
          with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hmem : ∀ l, l ∈ leavesEr acc1 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.fvar idx ty)) := by
          intro l
          rw [h2, hlv]
          simp only [leavesEr_cons, List.mem_cons]
          grind
        exact ⟨hmem, h3.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | app f a ihf iha =>
    intro G acc seen hseen hG
    have herase : (Expr.app f a)
        = Expr.app f a := rfl
    have hlv : (Expr.fvarLeaves (Expr.app f a))
        = (Expr.fvarLeaves f) ++ (Expr.fvarLeaves a) := by
      rw [herase, fvarLeaves_app]
    have hsz : (Expr.app f a).sizeF
        = f.sizeF + a.sizeF + 1 := by rw [herase]; rfl
    rw [Expr.fvarLeavesGoC.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.app f a)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGf : ∀ y, (G y ∨ y = (Expr.app f a)) →
            f.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := ihf (hseen.insertGray _) hGf
        rcases hp : Expr.fvarLeavesGoC acc (seen.insert _ ()) f with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGa : ∀ y, (G y ∨ y = (Expr.app f a)) →
            a.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := iha h3 hGa
        rcases hq : Expr.fvarLeavesGoC acc1 seen1 a with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.app f a)) := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | lam ty bd m iht ihb =>
    intro G acc seen hseen hG
    have herase : (Expr.lam ty bd m)
        = Expr.lam ty bd m := rfl
    have hlv : (Expr.fvarLeaves (Expr.lam ty bd m))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves bd) := by
      rw [herase, fvarLeaves_lam]
    have hsz : (Expr.lam ty bd m).sizeF
        = ty.sizeF + bd.sizeF + 1 := by rw [herase]; rfl
    rw [Expr.fvarLeavesGoC.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.lam ty bd m)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y, (G y ∨ y = (Expr.lam ty bd m)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht (hseen.insertGray _) hGt
        rcases hp : Expr.fvarLeavesGoC acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGb : ∀ y, (G y ∨ y = (Expr.lam ty bd m)) →
            bd.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := ihb h3 hGb
        rcases hq : Expr.fvarLeavesGoC acc1 seen1 bd with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.lam ty bd m)) := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | forallE ty bd m iht ihb =>
    intro G acc seen hseen hG
    have herase : (Expr.forallE ty bd m)
        = Expr.forallE ty bd m := rfl
    have hlv : (Expr.fvarLeaves (Expr.forallE ty bd m))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves bd) := by
      rw [herase, fvarLeaves_forallE]
    have hsz : (Expr.forallE ty bd m).sizeF
        = ty.sizeF + bd.sizeF + 1 := by rw [herase]; rfl
    rw [Expr.fvarLeavesGoC.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.forallE ty bd m)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y,
            (G y ∨ y = (Expr.forallE ty bd m)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht (hseen.insertGray _) hGt
        rcases hp : Expr.fvarLeavesGoC acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGb : ∀ y,
            (G y ∨ y = (Expr.forallE ty bd m)) →
            bd.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := ihb h3 hGb
        rcases hq : Expr.fvarLeavesGoC acc1 seen1 bd with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hmem : ∀ l, l ∈ leavesEr acc2 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.forallE ty bd m)) := by
          intro l
          rw [h5, h2, hlv, List.mem_append]
          grind
        exact ⟨hmem, h6.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | letE ty val bd iht ihv ihb =>
    intro G acc seen hseen hG
    have herase : (Expr.letE ty val bd)
        = Expr.letE ty val bd := rfl
    have hlv : (Expr.fvarLeaves (Expr.letE ty val bd))
        = (Expr.fvarLeaves ty) ++ (Expr.fvarLeaves val)
            ++ (Expr.fvarLeaves bd) := by
      rw [herase, fvarLeaves_letE]
    have hsz : (Expr.letE ty val bd).sizeF
        = ty.sizeF + val.sizeF + bd.sizeF + 1 := by
      rw [herase]; rfl
    rw [Expr.fvarLeavesGoC.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.letE ty val bd)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGt : ∀ y,
            (G y ∨ y = (Expr.letE ty val bd)) →
            ty.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := iht (hseen.insertGray _) hGt
        rcases hp : Expr.fvarLeavesGoC acc (seen.insert _ ()) ty with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hGv : ∀ y,
            (G y ∨ y = (Expr.letE ty val bd)) →
            val.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h5, h6⟩ := ihv h3 hGv
        rcases hq : Expr.fvarLeavesGoC acc1 seen1 val with ⟨acc2, seen2⟩
        rw [hq] at h5 h6
        have hGb : ∀ y,
            (G y ∨ y = (Expr.letE ty val bd)) →
            bd.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h8, h9⟩ := ihb h6 hGb
        rcases hr : Expr.fvarLeavesGoC acc2 seen2 bd with ⟨acc3, seen3⟩
        rw [hr] at h8 h9
        have hmem : ∀ l, l ∈ leavesEr acc3 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.letE ty val bd)) := by
          intro l
          rw [h8, h5, h2, hlv, List.mem_append, List.mem_append]
          grind
        exact ⟨hmem, h9.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩
  | proj s i sub ihe =>
    intro G acc seen hseen hG
    have herase : (Expr.proj s i sub)
        = Expr.proj s i sub := rfl
    have hlv : (Expr.fvarLeaves (Expr.proj s i sub))
        = (Expr.fvarLeaves sub) := by rw [herase, fvarLeaves_proj]
    have hsz : (Expr.proj s i sub).sizeF
        = sub.sizeF + 1 := by rw [herase]; rfl
    rw [Expr.fvarLeavesGoC.eq_def]
    split
    · rename_i hcut
      have : (Expr.fvarLeaves (Expr.proj s i sub)) = [] :=
        fvarLeaves_nil_of_fvarsBelow_zero _
          (fvarB_le (Nat.le_of_eq (by simpa using hcut)))
      exact ⟨by simp [this], hseen⟩
    · split
      · rename_i v hhit
        rcases hseen _ _ hhit with hsub | hgray
        · exact ⟨fun l => ⟨Or.inl, fun h => h.elim id (hsub l)⟩, hseen⟩
        · exact absurd (hG _ hgray) (Nat.lt_irrefl _)
      · dsimp only
        have hGs : ∀ y, (G y ∨ y = (Expr.proj s i sub)) →
            sub.sizeF < y.sizeF := by
          intro y hy
          rcases hy with hy | hy
          · have := hG y hy; omega
          · rw [hy]; omega
        obtain ⟨h2, h3⟩ := ihe (hseen.insertGray _) hGs
        rcases hp : Expr.fvarLeavesGoC acc (seen.insert _ ()) sub with ⟨acc1, seen1⟩
        rw [hp] at h2 h3
        have hmem : ∀ l, l ∈ leavesEr acc1 ↔
            l ∈ leavesEr acc ∨
              l ∈ (Expr.fvarLeaves (Expr.proj s i sub)) := by
          intro l
          rw [h2, hlv]
        exact ⟨hmem, h3.dropGray (fun l hl => (hmem l).mpr (Or.inr hl))⟩

/-! ### The base leaf list

`leafMem` compares annotations with `Expr`'s `==`, so on a
field-correct base list it decides `Expr`-level membership.  What the
subset walk needs of the base is exactly this pair of facts. -/

/-- A cached base leaf list is a faithful stand-in for an `Expr`-side
one: field-correct annotations, and the same *set* of erased leaves. -/
@[expose] def LeafBase (bl : List (Nat × Expr))
    (B' : List (Nat × Expr)) : Prop :=
  ∀ l, l ∈ leavesEr bl ↔ l ∈ B'

/-- `leafMem` decides membership in the erased list. -/
theorem leafMem_iff : ∀ {bl : List (Nat × Expr)},
    ∀ {idx : Nat} {ty : Expr},
      (Expr.leafMem bl idx ty = true ↔ (idx, (ty : Expr)) ∈ leavesEr bl) := by
  intro bl
  induction bl with
  | nil => intro idx ty; simp [Expr.leafMem]
  | cons p rest ih =>
    obtain ⟨i, t⟩ := p
    intro idx ty
    rw [show Expr.leafMem ((i, t) :: rest) idx ty
        = ((i == idx && (t == ty)) || Expr.leafMem rest idx ty)
      from rfl]
    rw [leavesEr_cons, List.mem_cons, Bool.or_eq_true, ih,
      Bool.and_eq_true, beq_iff_eq,
      beq_iff (a := t)]
    simp only [Prod.mk.injEq]
    grind

/-- …hence agrees with the `Expr`-side `contains` on a `LeafBase`. -/
theorem leafMem_spec {bl : List (Nat × Expr)}
    {B' : List (Nat × Expr)} (h : LeafBase bl B')
    {idx : Nat} {ty : Expr} :
    Expr.leafMem bl idx ty = B'.contains (idx, (ty : Expr)) := by
  rw [Bool.eq_iff_iff, List.contains_eq_mem, decide_eq_true_iff,
    leafMem_iff, h]

/-- The base list built by the leaf walk *is* a `LeafBase` for the
erasure's leaves. -/
theorem fvarLeavesC_leafBase {base : Expr} :
    LeafBase (Expr.fvarLeavesC base) (Expr.fvarLeaves base) := by
  obtain ⟨h2, -⟩ := fvarLeavesGoC_spec (e := base)
    (G := fun _ => False) (acc := []) (seen := {})
    SeenInv.empty (by intro y hy; exact hy.elim)
  intro l
  simp only [Expr.fvarLeavesC, h2]
  simp

/-! ### The subset walk -/

/-- The walk's cutoff, read as the specification: a node whose cached
fvar range is zero has no leaf to check. -/
private theorem leavesSubP_cut_spec {B' : List (Nat × Expr)} {e : Expr}
    (h : (e.fvarB == 0) = true) :
    true = ((Expr.fvarLeaves e).all fun l => B'.contains l) := by
  rw [fvarLeaves_nil_of_fvarsBelow_zero _
    (fvarB_le (Nat.le_of_eq (by simpa using h)))]
  rfl

/-- **The plain descent decides the `Expr`-level leaf-subset
boolean.** -/
theorem leavesSubP_spec {bl : List (Nat × Expr)} {B' : List (Nat × Expr)}
    (hbl : LeafBase bl B') : ∀ {e : Expr},
    Expr.leavesSubP bl e = ((Expr.fvarLeaves e).all fun l => B'.contains l) := by
  intro e
  induction e with
  | bvar i =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp [fvarLeaves_bvar]
  | sort u =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp [fvarLeaves_sort]
  | const n us =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp [fvarLeaves_const]
  | lit l =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp [fvarLeaves_lit]
  | fvar idx ty iht =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp only [fvarLeaves_fvar, List.all_cons, leafMem_spec hbl, iht]
  | app f a ihf iha =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp only [fvarLeaves_app, List.all_append, ihf, iha]
  | lam ty bd m iht ihb =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp only [fvarLeaves_lam, List.all_append, iht, ihb]
  | forallE ty bd m iht ihb =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp only [fvarLeaves_forallE, List.all_append, iht, ihb]
  | letE ty val bd iht ihv ihb =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp only [fvarLeaves_letE, List.all_append, iht, ihv, ihb]
  | proj s i sub ihe =>
    rw [Expr.leavesSubP.eq_def]; split
    · next h => exact leavesSubP_cut_spec h
    · simp only [fvarLeaves_proj, ihe]

/-- **The cached leaf-subset test decides the `Expr`-level
leaf-subset boolean.** -/
private theorem leavesSubC_spec {bl : List (Nat × Expr)} {B' : List (Nat × Expr)}
    (hbl : LeafBase bl B') {e : Expr} :
    Expr.leavesSubC bl e = ((Expr.fvarLeaves e).all fun l => B'.contains l) := by
  rw [Expr.leavesSubC.eq_def]
  split
  · next h => exact leavesSubP_cut_spec h
  · rw [Expr.resBool_eq]; exact leavesSubP_spec hbl

/-- **The fabrication leaf guard agrees with the `Expr`-level
leaf-subset boolean** — `leafGuard_spec'`'s right-hand side, verbatim,
with the arena denotation replaced by the erasure. -/
theorem leafGuard_spec {fab base : Expr} :
    Expr.leafGuard fab base
      = ((Expr.fvarLeaves fab).all
          fun l => (Expr.fvarLeaves base).contains l) := by
  unfold Expr.leafGuard
  cases hhf : fab.hasFvar with
  | false =>
    have : (Expr.fvarLeaves fab) = [] :=
      fvarLeaves_nil_of_fvarsBelow_zero _
        (Expr.fvarsBelow_iff.mpr
          (Nat.le_of_eq (Expr.hasFvar_eq_false_iff.mp hhf)))
    simp [this]
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    exact leavesSubC_spec fvarLeavesC_leafBase

end ConLeche.Expr

namespace ConLeche.Cached

open ConLeche

/-! ## Guard agreement

The environment-index guards of `ConLeche/Cached/StateC.lean` are pure
functions of the node, so each agrees with its `Expr`-side original.
Each comes in two forms: the plain equation, and (primed) the same
equation transported along the value equation the simulation
carries. -/

open Expr in
/-- The `Nat`-literal readout agrees with the spec's `rawNatLit?` on
the erasure — a top-level match, so no invariant is needed. -/
theorem rawNatLitC?_spec (e : Expr) :
    rawNatLitC? e = rawNatLit? e := by
  cases e with
  | lit l => cases l <;> rfl
  | const c us =>
    cases us with
    | nil =>
      show (if c == natZeroName then some 0 else none)
        = (if c = natZeroName then some 0 else none)
      by_cases hc : c = natZeroName <;> simp [hc]
    | cons u us => rfl
  | _ => rfl

open Expr in
/-- `rawNatLitC?_spec` transported along the value equation the
simulation carries. -/
theorem rawNatLitC?_spec' {w : Expr} {wx : Expr}
    (h : w = wx) : rawNatLitC? w = rawNatLit? wx := by
  rw [rawNatLitC?_spec, h]

open Expr in
/-- The unit-like-type guard agrees with the spec's `isUnitLikeTy` on
the erasure — again a top-level match on the whnf'd node, so no
invariant is needed; only the `FEnv` index has to be resolved. -/
theorem isUnitLikeTyC_spec {env : Env} (e : Expr) :
    isUnitLikeTyC (mkFEnv env) e = isUnitLikeTy env e := by
  cases e with
  | const cn us =>
    show (cn == punitName &&
      (match (mkFEnv env).find? punitName with
        | some (.indInfo _ _) => true
        | _ => false) &&
      (match (mkFEnv env).find? punitRecName with
        | some (.recInfo _ mI rP [r]) => mI == rP && r.nfields == 0
        | _ => false)) = _
    rw [mkFEnv_find?, mkFEnv_find?]
    rfl
  | _ => rfl

open Expr in
/-- `isUnitLikeTyC_spec` transported along the value equation. -/
theorem isUnitLikeTyC_spec' {env : Env} {w : Expr} {wx : Expr}
    (h : w = wx) :
    isUnitLikeTyC (mkFEnv env) w = isUnitLikeTy env wx := by
  rw [isUnitLikeTyC_spec, h]

open Expr in
/-- The constructor-application guard agrees with the spec's
`isCtorApp` on the erasure.  Unlike the two above it reads the
*spine head*. -/
theorem isCtorAppC_spec {env : Env} {e : Expr} :
    isCtorAppC (mkFEnv env) e = isCtorApp env e := by
  show (match Expr.getAppFn e with
      | .const cn _ =>
        match (mkFEnv env).find? cn with
        | some (.ctorInfo _ _ _) => true
        | _ => false
      | _ => false) = _
  rw [isCtorApp]
  cases Expr.getAppFn e with
  | const cn us =>
    show (match (mkFEnv env).find? cn with
        | some (.ctorInfo _ _ _) => true
        | _ => false) = _
    rw [mkFEnv_find?]
    rfl
  | _ => rfl

open Expr in
/-- `isCtorAppC_spec` transported along the value equation. -/
theorem isCtorAppC_spec' {env : Env} {e : Expr} {ex : Expr}
    (h : e = ex) :
    isCtorAppC (mkFEnv env) e = isCtorApp env ex := by
  rw [isCtorAppC_spec, h]

/-- `Expr.quickPair` transported along the value equations. -/
theorem quickPair_spec' {a b : Expr} {ax bx : Expr}
    (ha : a = ax) (hb : b = bx) : Expr.quickPair a b = Expr.quickPair ax bx := by
  rw [ha, hb]

/-- The eta constructor-shape gate agrees with the spec's `etaCtorShape`
(`Expr = Expr`; only the environment lookup differs). -/
theorem etaCtorShapeC_spec' {env : Env} {e : Expr} {ex : Expr}
    (h : e = ex) :
    etaCtorShapeC (mkFEnv env) e = etaCtorShape env ex := by
  subst h
  unfold etaCtorShapeC etaCtorShape
  generalize Expr.getAppFn e = f
  cases f <;> simp only [mkFEnv_find?] <;> first
    | rfl
    | (generalize env.find? _ = ci
       rcases ci with _ | ci <;> try rfl
       cases ci <;> rfl)

open Expr in
/-- The reducibility-hint readout agrees with the spec's `headHint` on
the erasure — like `isCtorAppC_spec` it reads the *spine head*, so the
node invariant is needed. -/
theorem headHintC_spec {env : Env} {e : Expr} :
    headHintC (mkFEnv env) e = headHint env e := by
  show (match Expr.getAppFn e with
      | .const nm _ =>
        match (mkFEnv env).find? nm with
        | some (.defnInfo _ _ hint) => hint
        | _ => .opaque
      | _ => .opaque) = _
  rw [headHint]
  cases Expr.getAppFn e with
  | const nm us =>
    dsimp only
    rw [mkFEnv_find?]
    cases env.find? nm with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

open Expr in
/-- `headHintC_spec` transported along the value equation. -/
theorem headHintC_spec' {env : Env} {e : Expr} {ex : Expr}
    (h : e = ex) :
    headHintC (mkFEnv env) e = headHint env ex := by
  rw [headHintC_spec, h]

open Expr in
/-- The lazy-delta unfoldability decision agrees with the spec's
`unfoldableHead` on the erasure (again a spine-head read). -/
theorem unfoldableHeadC_spec {env : Env} {e : Expr} :
    unfoldableHeadC (mkFEnv env) e = unfoldableHead env e := by
  show (match Expr.getAppFn e with
      | .const nm us =>
        match (mkFEnv env).find? nm with
        | some (.defnInfo cv _ _) => us.length == cv.levelParams.length
        | _ => false
      | _ => false) = _
  rw [unfoldableHead]
  cases Expr.getAppFn e with
  | const nm us =>
    dsimp only
    rw [mkFEnv_find?]
    cases env.find? nm with
    | none => rfl
    | some ci => cases ci <;> rfl
  | _ => rfl

open Expr in
/-- `unfoldableHeadC_spec` transported along the value equation. -/
theorem unfoldableHeadC_spec' {env : Env} {e : Expr} {ex : Expr}
    (h : e = ex) :
    unfoldableHeadC (mkFEnv env) e = unfoldableHead env ex := by
  rw [unfoldableHeadC_spec, h]

/-- **The `And`-rescue gate through the index is the spec's gate**:
both sides are `andRescueSlotsOf` at a lookup, and the index's lookup
is `Env.findProj?` (`mkFEnv_findProj?`). -/
theorem andRescueSlotsF_spec {env : Env} {ctor : Name} {nP : Nat}
    {ust : List Level} :
    (mkFEnv env).andRescueSlotsF ctor nP ust = andRescueSlots env ctor nP ust := by
  unfold FEnv.andRescueSlotsF andRescueSlots
  have : (mkFEnv env).findProj? = env.findProj? := by
    funext T i; exact mkFEnv_findProj? env T i
  rw [this]

open Expr in
/-- The same-constant-head short-circuit agrees with the spec's
`sameConstHeads` on the erasures: both sides must be applications, and
then the two *function parts'* spine heads are compared. -/
theorem sameConstHeadsC_spec {a b : Expr} :
    sameConstHeadsC a b = sameConstHeads a b := by
  cases a with
  | app f₁ a₁ =>
    cases b with
    | app f₂ a₂ =>
      show (match Expr.getAppFn f₁, Expr.getAppFn f₂ with
          | .const n₁ _, .const n₂ _ => n₁ == n₂
          | _, _ => false) = _
      rw [show sameConstHeads ((Expr.app f₁ a₁))
              ((Expr.app f₂ a₂))
            = (match (Expr.getAppFn f₁), (Expr.getAppFn f₂) with
              | .const n₁ _, .const n₂ _ => n₁ == n₂
              | _, _ => false) from rfl]
    | _ => rfl
  | _ => cases b <;> rfl

open Expr in
/-- `sameConstHeadsC_spec` transported along the value equations. -/
theorem sameConstHeadsC_spec' {a b : Expr} {xa xb : Expr}
    (h₁ : a = xa) (h₂ : b = xb) :
    sameConstHeadsC a b = sameConstHeads xa xb := by
  rw [sameConstHeadsC_spec, h₁, h₂]

open Expr in
/-- The `O(1)` eager fvar-range field is exact (`fvarB_eq _`), so its
non-zeroness is the spec's `Expr.hasFvar`. -/
theorem hasFvar_spec' {e : Expr} {ex : Expr}
    (h : e = ex) : Expr.hasFvar e = ex.hasFvar := by
  rw [h]

open Expr in
/-- `Expr.wscopedBC_spec` transported along the value equation. -/
theorem wscopedB_spec' {d : Nat} {e : Expr} {ex : Expr}
    (h : e = ex) :
    Expr.wscopedBC d e = ex.wscopedB d := by
  rw [Expr.wscopedBC_spec, h]

open Expr in
/-- `Expr.looseBVarsBounded` transported along the value equation. -/
theorem looseBVarsBounded_spec' {k : Nat} {e : Expr}
    {ex : Expr} (h : e = ex) :
    Expr.looseBVarsBounded k e = ex.looseBVarsBounded k := by
  rw [h]

open Expr in
/-- `Expr.leafGuard_spec` transported along the value equations. -/
theorem leafGuard_spec' {fab base : Expr} {fx bx : Expr}
    (h₁ : fab = fx) (h₂ : base = bx) :
    Expr.leafGuard fab base
      = (fx.fvarLeaves.all fun l => bx.fvarLeaves.contains l) := by
  rw [Expr.leafGuard_spec, h₁, h₂]

/-! ## Constant resolution

`constsResolveFC` (`ConLeche/Cached/StateC.lean`) is the cached
`Expr.constsResolveF`: the pointer-keyed walk of
`ConLeche/Cached/ExprOpsC.lean` with **no** cutoff (the environment
index is an ambient parameter of the call, so only the node matters).
The walk carries its own proof against the plain descent
`constsResolveFP`, so all that is proved here is that plain
descent. -/

/-- **The plain descent is `Expr.constsResolveF`.** -/
theorem constsResolveFP_spec {fe : FEnv} : ∀ {e : Expr},
    constsResolveFP fe e = Expr.constsResolveF fe e := by
  intro e
  induction e with
  | bvar i => rw [constsResolveFP, Expr.constsResolveF]
  | sort u => rw [constsResolveFP, Expr.constsResolveF]
  | lit l => cases l <;> rw [constsResolveFP, Expr.constsResolveF]
  | const n us => rw [constsResolveFP, Expr.constsResolveF]
  | fvar idx ty iht => rw [constsResolveFP, Expr.constsResolveF, iht]
  | app f a ihf iha => rw [constsResolveFP, Expr.constsResolveF, ihf, iha]
  | lam ty bd m iht ihb => rw [constsResolveFP, Expr.constsResolveF, iht, ihb]
  | forallE ty bd m iht ihb => rw [constsResolveFP, Expr.constsResolveF, iht, ihb]
  | letE ty val bd iht ihv ihb =>
    rw [constsResolveFP, Expr.constsResolveF, iht, ihv, ihb]
  | proj s i sub ihe => rw [constsResolveFP, Expr.constsResolveF, ihe]

open Expr in
/-- **`constsResolveFC` is `Expr.constsResolveF` of the erasure.** -/
theorem constsResolveFC_spec {fe : FEnv} {e : Expr} :
    constsResolveFC fe e = Expr.constsResolveF fe e := by
  rw [constsResolveFC.eq_def, Expr.resBool_eq]
  exact constsResolveFP_spec

/-! ### The zero-ness readout (task #163, batch 9; task #272)

The binder-telescope loops used to read the zero-ness datum out of a
`Level`-keyed memo (`PWMemo`/`zeronessOfLGo`), with a correspondence
battery here saying an entry *is* the readout of its key.  Task #272
deleted the table: the `inferPisOutI` fold THREADS the datum (every
node of a ∀ telescope shares it, `zeronessOf (imax u v) = zeronessOf
v`), where the memo missed on every node and paid the readout over the
growing level; the three remaining readouts are one call each, and the
mirror reads `Level.zeronessOf` directly, so their agreement is
`rfl`. -/

end ConLeche.Cached
