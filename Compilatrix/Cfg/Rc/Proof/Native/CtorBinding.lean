import Compilatrix.Cfg.Rc.Proof.Native.Allocation
import Compilatrix.Cfg.Rc.Proof.Native.Indices

/-! The runtime constructor index refers to the same first matching table row
used by Fir.CtorInfo.ofKey. Filtering fieldless constructors cannot change a
positive first match. No unstated uniqueness assumption on table keys is used. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native.Spec

private theorem find_filter_keep {α : Type} {xs : List α} {p q : α → Bool} {x : α}
    (found : xs.find? p = some x) (keep : q x = true) :
    (xs.filter q).find? p = some x := by
  obtain ⟨hx, before, after, equal, earlier⟩ := List.find?_eq_some_iff_append.mp found
  rw [equal, List.filter_append, List.filter_cons, keep]
  simp only [↓reduceIte]
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨hx, before.filter q, after.filter q, rfl, ?_⟩
  intro a ha
  exact earlier a (List.mem_filter.mp ha).1

theorem table_row {table : List Lam.CtorInfo} {c : Fir.CtorInfo}
    (accepted : Fir.CtorInfo.ofKey table c.key = some c) :
    ∃ row, table.find? (fun r => r.key == c.key) = some row ∧
      row.tag = c.tag ∧ row.arity = c.arity ∧
      c.fieldKinds = List.replicate c.arity .shared := by
  cases hf : table.find? (fun r => r.key == c.key) with
  | none => simp [Fir.CtorInfo.ofKey, hf] at accepted
  | some row =>
    have equal : ({
        key := c.key, tag := row.tag, nobj := row.arity
        fieldKinds := List.replicate row.arity .shared } : Fir.CtorInfo) = c := by
      simpa [Fir.CtorInfo.ofKey, hf] using accepted
    have arity : row.arity = c.arity := by
      simpa only [Fir.CtorInfo.arity, Nat.add_zero] using congrArg Fir.CtorInfo.arity equal
    refine ⟨row, rfl, congrArg Fir.CtorInfo.tag equal, arity, ?_⟩
    simpa only [arity] using (congrArg Fir.CtorInfo.fieldKinds equal).symm

theorem ctorIndex_row {l : Layout} {key : Key.CtorKey} {index : Nat}
    (selected : ctorIndex l key = some index) :
    ∃ row, l.ctors[index]? = some row ∧
      l.ctors.find? (fun r => r.key == key) = some row := by
  cases hf : l.ctors.zipIdx.find? (fun p => p.1.key == key) with
  | none => simp [ctorIndex, hf] at selected
  | some pair =>
    obtain ⟨row, i⟩ := pair
    simp only [ctorIndex, hf, Option.map_some, Option.some.injEq] at selected
    subst index
    have hm := List.mem_of_find?_eq_some hf
    have hget : l.ctors[i]? = some row := by
      simpa using List.mem_zipIdx_iff_getElem?.mp hm
    refine ⟨row, hget, ?_⟩
    calc
      l.ctors.find? (fun r => r.key == key) =
          (l.ctors.zipIdx.map Prod.fst).find? (fun r => r.key == key) := by
        rw [List.zipIdx_map_fst]
      _ = some row := by
        rw [List.find?_map]
        change (l.ctors.zipIdx.find? (fun p => p.1.key == key)).map Prod.fst = some row
        rw [hf]
        rfl

theorem ctorIndex_binding {P : Program} {c : Fir.CtorInfo} {index : Nat}
    (accepted : Fir.CtorInfo.ofKey P.base.ctors c.key = some c)
    (positive : 0 < c.arity)
    (selected : ctorIndex (layoutOf P) c.key = some index) :
    ∃ row, (layoutOf P).ctors[index]? = some row ∧
      row.tag = c.tag ∧ row.arity = c.arity ∧
      c.fieldKinds = List.replicate c.arity .shared := by
  obtain ⟨expected, hfind, htag, harity, hshared⟩ := table_row accepted
  have filtered : (layoutOf P).ctors.find? (fun r => r.key == c.key) = some expected :=
    find_filter_keep hfind (by simpa [harity] using positive)
  obtain ⟨actual, hget, hactual⟩ := ctorIndex_row selected
  rw [filtered] at hactual
  cases hactual
  exact ⟨expected, hget, htag, harity, hshared⟩

theorem consume_allocation_runtime {P : Program} {x main : Nat}
    {c : Fir.CtorInfo} {args : List Fir.Arg} {kind : Own.Kind} {result : Instr}
    {funcs : List Lir.Func} (hlen : funcs.length = P.base.size)
    (positive : 0 < c.arity)
    (accepted : consume P (layoutOf P) (.bind x (.alloc c args kind)) = .ok result) :
    ∃ index, result = .bind x (.fir (.call ((layoutOf P).allocWrapper index) args)) ∧
      (rawProgram (layoutOf P) funcs main).funcs[(layoutOf P).allocWrapper index]? =
        some (allocationWrapper ((layoutOf P).allocProc index) c.arity) ∧
      (rawProgram (layoutOf P) funcs main).funcs[(layoutOf P).allocProc index]? =
        some (Rt.Rc.Procs.alloc c.arity c.tag) := by
  obtain ⟨_, _, _, _, _, table, _, _, _, _, _, index, hi, resultEq⟩ :=
    consume_allocation positive accepted
  obtain ⟨row, hrow, htag, harity, _⟩ := ctorIndex_binding table positive hi
  refine ⟨index, resultEq, ?_, ?_⟩
  · simpa only [harity] using raw_alloc_wrapper hlen main index hrow
  · simpa only [harity, htag] using raw_alloc_proc hlen main index hrow





end Compilatrix.Cfg.Rc.Native.Spec
