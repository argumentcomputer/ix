import IxCC.Xv.Stacking.Run

/-!
# Stacking's lookups and placements are their first forms

`run` reads a callee's declared result count at every call and tail call,
and places wrappers and functions one after another. The first forms read
the count from the function array converted to a list (`resultsOfList`,
`tailResultsList`: linear in the function count at every site) and appended
each placement to the list built so far (`placeExportsList`,
`placeFuncsList`: quadratic). The definitions `run` uses read the array and
build each list in one pass; they are equal to the first forms
(`resultsOf_eq_list`, `tailResults_eq_list`, `placeExports_eq_list`,
`placeFuncs_eq_list`), so every lemma about them keeps its statement and
rewrites by the equality.
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.Lir (FunId)
open IxCC.Xv.Stacking

theorem resultsOf_eq_list (p : LProgram) (g : FunId) : resultsOf p g = resultsOfList p g := by
  simp only [resultsOf, resultsOfList, Array.getElem?_toList]

theorem tailResults_eq_list (p : LProgram) (f : Func Loc) : tailResults p f = tailResultsList p f := by
  simp only [tailResults, tailResultsList, resultsOf, Array.getElem?_toList]

/-- Putting each item in front, then reversing, is appending each item. -/
theorem foldl_cons_rev {α β : Type} (mk : α → Nat → β) (sz : α → Nat) :
    ∀ (xs : List α) (acc : List β) (n : Nat),
      xs.foldl (fun (p : List β × Nat) x => (mk x p.2 :: p.1, p.2 + sz x)) (acc, n) =
        ((xs.foldl (fun (p : List β × Nat) x => (p.1 ++ [mk x p.2], p.2 + sz x)) (acc.reverse, n)).1.reverse,
         (xs.foldl (fun (p : List β × Nat) x => (p.1 ++ [mk x p.2], p.2 + sz x)) (acc.reverse, n)).2)
  | [], acc, n => by simp
  | x :: xs, acc, n => by
      simp only [List.foldl_cons]
      rw [foldl_cons_rev mk sz xs (mk x n :: acc) (n + sz x), List.reverse_cons]

theorem placeExports_eq_list (exports : List (FunId × String × List ArgRep × Func Loc)) :
    placeExports exports = placeExportsList exports := by
  unfold placeExports placeExportsList
  rw [foldl_cons_rev (fun (e : FunId × String × List ArgRep × Func Loc) n =>
      ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
    (fun e => wrapperBlocks e.2.2.1)]
  simp only [List.reverse_nil, List.reverse_reverse]

theorem placeFuncs_eq_list (fns : List (Func Loc × FunId × FrameLayout × Facts)) (next : Nat) :
    placeFuncs fns next = placeFuncsList fns next := by
  unfold placeFuncs placeFuncsList
  rw [foldl_cons_rev (fun (e : Func Loc × FunId × FrameLayout × Facts) n =>
      ({ func := e.1, fn := e.2.1, layout := e.2.2.1, facts := e.2.2.2, start := n } : Placed))
    (fun e => funcBlocks e.1 e.2.2.1 e.2.2.2)]
  simp only [List.reverse_nil, List.reverse_reverse]

end IxCC.Xv.Stacking.Proof
