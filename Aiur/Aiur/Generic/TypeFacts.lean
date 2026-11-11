import Aiur.Generic.AST

namespace Aiur.Generic

@[simp] theorem Ty.subst_nil (type : Ty) : type.subst [] = type := by
  have sub (t : Ty) (smaller : sizeOf t < sizeOf type) : t.subst [] = t :=
    Ty.subst_nil t
  cases type with
  | field | param => simp [Ty.subst]
  | ptr t | array t n => simp only [Ty.subst, sub t (by simp_wf <;> omega)]
  | tuple ts | named n ts =>
      have items : ts.map (Ty.subst []) = ts := by
        calc
          ts.map (Ty.subst []) = ts.map id := by
            apply List.map_congr_left
            intro t ht
            exact sub t (by simp_wf; have := List.sizeOf_lt_of_mem ht; omega)
          _ = ts := List.map_id ts
      simp only [Ty.subst, items]
termination_by sizeOf type
decreasing_by exact smaller

end Aiur.Generic
