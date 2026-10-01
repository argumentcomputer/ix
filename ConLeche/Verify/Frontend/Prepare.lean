module

public import ConLeche.Frontend.Prepare

/- Proof code is private by default (CLAUDE.md): this module's `def`
bodies are the frontend's, and nothing here is unfolded elsewhere. -/
public section

/-!
# What `preparePrelude` does to the file's records (task #293)

The decoder emits the file's declaration records; `preparePrelude`
turns that array into the one the fold runs over
(`ConLeche/Frontend/Prepare.lean`).  The maintainer's ruling asked for
a spec simple enough to state in one line, and this is it:

    ∃ extra ⊆ prelude, (preparePrelude pre ds).toList.Perm (ds.toList ++ extra)

**every record of the file is in the prepared stream, unchanged and
exactly once**, and what else is there is a prelude record the file did
not declare.  The two steps are both reorderings — the stream's own
prelude declarations are MOVED to the front rather than duplicated, and
the ground hoist moves a pinned operation's ground ahead of it — so
nothing is dropped, nothing is rewritten, and no verdict is decided
here.

The pass-through corollary `mem_preparePrelude` is what a statement
about the FILE composes with: a record the file declares is a record
the fold sees.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Pulling the stream's own copy out -/

/-- `pickSpec`, by index: the first record declaring `n` is the one at
`findIdx`, and what is left is the list with that index erased — the
shape the array implementation computes.  Where no record declares
`n`, `findIdx` is the length, `getElem?` is `none` and `eraseIdx`
changes nothing. -/
theorem pickSpec_eq (n : Name) : ∀ l : List Declaration,
    pickSpec n l = (l[l.findIdx (declares n)]?, l.eraseIdx (l.findIdx (declares n)))
  | [] => rfl
  | d :: ds => by
    simp only [pickSpec, List.findIdx_cons]
    by_cases h : declares n d
    · simp [h]
    · simp only [h, if_false, Bool.false_eq_true]
      rw [pickSpec_eq n ds]
      simp

/-- **The implementation is its specification**: the array pick is the
list pick, on the array's records. -/
theorem pick_toList (n : Name) (ds : Array Declaration) :
    ((pick n ds).1, (pick n ds).2.toList) = pickSpec n ds.toList := by
  rw [pickSpec_eq]
  cases ds
  simp [pick]

/-- What `pickSpec` removes and what it leaves is a permutation of what
it was given. -/
theorem pickSpec_perm (n : Name) : ∀ l : List Declaration,
    ((pickSpec n l).1.toList ++ (pickSpec n l).2).Perm l
  | [] => by simp [pickSpec]
  | d :: ds => by
    simp only [pickSpec]
    by_cases h : declares n d
    · simp [h]
    · simp only [h, if_false, Bool.false_eq_true]
      exact (List.perm_middle (a := d)
        (l₁ := (pickSpec n ds).1.toList) (l₂ := (pickSpec n ds).2)).trans
        ((pickSpec_perm n ds).cons d)

/-! ## The prelude's declarations, in front -/

/-- **The implementation is its specification**: the array front-builder
is `frontSpec`, its accumulator in front. -/
theorem frontOf_toList : ∀ (ps : List Declaration) (acc ds : Array Declaration),
    (frontOf acc ps ds).1.toList = acc.toList ++ (frontSpec ps ds.toList).1 ∧
      (frontOf acc ps ds).2.toList = (frontSpec ps ds.toList).2
  | [], acc, ds => by simp [frontOf, frontSpec]
  | p :: ps, acc, ds => by
    have hpick := pick_toList (preludeKey p) ds
    simp only [Prod.ext_iff] at hpick
    obtain ⟨hfst, hsnd⟩ := hpick
    obtain ⟨h₁, h₂⟩ := frontOf_toList ps (acc.push ((pick (preludeKey p) ds).1.getD p))
      (pick (preludeKey p) ds).2
    simp only [frontOf, frontSpec, h₁, h₂]
    simp only [hsnd, hfst, Array.toList_push, List.append_assoc, List.cons_append,
      List.nil_append, and_self]

/-- **The front is the prelude's declarations, and what it took it took
from the stream.** -/
theorem frontSpec_perm : ∀ (ps ds : List Declaration),
    ∃ extra : List Declaration, (∀ d ∈ extra, d ∈ ps) ∧
      ((frontSpec ps ds).1 ++ (frontSpec ps ds).2).Perm (ds ++ extra)
  | [], ds => ⟨[], by simp, by simp [frontSpec]⟩
  | p :: ps, ds => by
    obtain ⟨extra, hextra, hperm⟩ := frontSpec_perm ps (pickSpec (preludeKey p) ds).2
    have hpick := pickSpec_perm (preludeKey p) ds
    simp only [frontSpec]
    cases hm : (pickSpec (preludeKey p) ds).1 with
    | some x =>
      refine ⟨extra, fun d hd => List.mem_cons_of_mem _ (hextra d hd), ?_⟩
      rw [hm] at hpick
      simp only [Option.getD_some, List.cons_append]
      refine (hperm.cons x).trans ?_
      have : (x :: ((pickSpec (preludeKey p) ds).2 ++ extra)) =
          (x :: (pickSpec (preludeKey p) ds).2) ++ extra := rfl
      rw [this]
      exact List.Perm.append_right extra (by simpa using hpick)
    | none =>
      refine ⟨p :: extra, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hextra d hd')
      · rw [hm] at hpick
        simp only [Option.getD_none, List.cons_append]
        have hds : (pickSpec (preludeKey p) ds).2.Perm ds := by simpa using hpick
        exact ((hperm.cons p).trans ((hds.append_right extra).cons p)).trans
          List.perm_middle.symm

/-! ## The ground hoist -/

/-- The records of an array, read off by index, are the array. -/
theorem range_map_getElem! (a : Array Declaration) :
    (List.range a.size).map (fun k => a[k]!) = a.toList := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < a.size := by simpa using h₂
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact getElem!_pos a i hi

/-- **The reorder is a permutation.**  The sort is `List.mergeSort`
exactly so that this line exists (`List.mergeSort_perm`). -/
theorem applyHoist_perm (ds : Array Declaration) (target : Std.HashMap Nat Nat) :
    (applyHoist ds target).1.toList.Perm ds.toList := by
  simp only [applyHoist]
  rw [← range_map_getElem! ds]
  exact (List.mergeSort_perm _ _).map _

/-- **The hoist is a permutation**: it moves records, it never adds or
drops one. -/
theorem hoistNatOpGround_perm (ds : Array Declaration) :
    (hoistNatOpGround ds).1.toList.Perm ds.toList := by
  simp only [hoistNatOpGround]
  split
  · exact List.Perm.refl _
  · exact applyHoist_perm ds _

/-! ## The prepared stream -/

/-- **THE SPEC** (maintainer, task #293): *"it is a permutation of the
input plus additional declarations, but nothing missing"* — and the
additional declarations are the built-in prelude's own records. -/
theorem preparePrelude_perm (pre : PreludeIx) (ds : Array Declaration) :
    ∃ extra : List Declaration, (∀ d ∈ extra, d ∈ pre.decls.toList) ∧
      (preparePrelude pre ds).toList.Perm (ds.toList ++ extra) := by
  obtain ⟨extra, hextra, hperm⟩ := frontSpec_perm pre.decls.toList ds.toList
  refine ⟨extra, hextra, ?_⟩
  obtain ⟨h₁, h₂⟩ := frontOf_toList pre.decls.toList #[] ds
  simp only [preparePrelude, prepareD]
  refine (hoistNatOpGround_perm _).trans ?_
  rw [Array.toList_append, h₁, h₂]
  simpa using hperm

/-- **The pass-through**: every record of the file is a record of the
fold's input, unchanged.  This is what a statement about the FILE
composes with. -/
theorem mem_preparePrelude {pre : PreludeIx} {ds : Array Declaration}
    {pd : Declaration} (h : pd ∈ ds) : pd ∈ preparePrelude pre ds := by
  obtain ⟨extra, -, hperm⟩ := preparePrelude_perm pre ds
  exact Array.mem_toList_iff.mp
    (hperm.mem_iff.mpr (List.mem_append_left _ (Array.mem_toList_iff.mpr h)))

end ConLeche.Frontend
