import IxCC.Rt.Proof.OpsAlloc

/-!
# Projections and copies

`proj_sim`: `Rt.lower`'s projection of field `i` is a load at `8 + 8i` from
the cell (the cells of the heap invariant hold related words there); the
`Nat` successor's field is `v − 2` (no cell has a `Nat` key, so the
scrutinee is a successor literal). `arg_sim`: a copy is a copy.
-/

set_option autoImplicit false

namespace IxCC.Rt.Proof

open IxCC.Lir (Word)
open IxCC.Rt.Lower
open IxCC.Src (NatMap)

/-! ## Cfg's side -/

/-- A projection's Cfg meaning. -/
theorem evalRhs_proj {T : Own.Tables} {ρ : Own.Env} {H H' : Own.Heap} {y : Nat} {c : Key.CtorKey} {i : Nat}
    {v : Own.RVal} (h : Own.evalRhs .immortal T ρ H (.proj y c i) = .ok (v, H')) :
    H' = H ∧ ∃ u fs, ρ.get? y = some u ∧ u.asCtor T.known H = some (c, fs) ∧ fs[i]? = some v := by
  simp only [Own.evalRhs] at h
  cases hu : ρ.get? y with
  | none => simp [hu] at h
  | some u =>
    simp only [hu] at h
    cases ha : u.asCtor T.known H with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨c', fs⟩ := p
      simp only [ha] at h
      split at h
      · rename_i hc
        subst hc
        cases hf : fs[i]? with
        | none => simp [hf, Sem.Result.ofOption, Sem.Result.map, Sem.Result.bind] at h
        | some w =>
          simp only [hf, Sem.Result.ofOption, Sem.Result.map, Sem.Result.bind, Sem.Result.ok.injEq,
            Prod.mk.injEq] at h
          exact ⟨h.2.symm, u, fs, rfl, ha, by rw [hf, h.1]⟩
      · simp at h

/-- A copy's Cfg meaning. -/
theorem evalRhs_arg {T : Own.Tables} {ρ : Own.Env} {H H' : Own.Heap} {a : Fir.Arg} {v : Own.RVal}
    (h : Own.evalRhs .immortal T ρ H (.fir (.arg a)) = .ok (v, H')) : H' = H ∧ Own.evalArg ρ a = some v := by
  simp only [Own.evalRhs] at h
  cases ha : Own.evalArg ρ a with
  | none => simp [ha] at h
  | some w =>
    simp only [ha, Sem.Result.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, by rw [h.1]⟩

/-- A cell's constructor is not `Nat`'s. -/
theorem cell_notNat {T : Tables} {P : List Word} {H : Own.Heap} {ctx : Word} {m : X86.Memory}
    (hheap : HeapInv T P H ctx m) {ℓ : Nat} {w : Word} (hP : P[ℓ]? = some w) {rc : Nat} {mode : Own.OMode}
    {b : Own.Body} (hH : H.cells[ℓ]? = some (.live rc mode b)) :
    T.known.natZero ≠ some b.ctor.key ∧ T.known.natSucc ≠ some b.ctor.key ∧ CellAt T P m w b := by
  obtain ⟨bump, limit, hA⟩ := hheap
  obtain ⟨-, hc, -, -⟩ := hA.cell hP hH
  have hn := hc.ctor.notNat
  simp only [isNatKey, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hn
  exact ⟨hn.1, hn.2, hc⟩

/-! ## The lowering's side -/

theorem proj_run {f : Fir.FunId} {T : Tables} {x y : Nat} {c : Key.CtorKey} {i : Nat} {st st' : St}
    (h : (Lower.proj f T x y c i).run st = .ok ((), st')) :
    (T.known.natSucc = some c ∧ i = 0 ∧
      st' = { st with acc := [.assign x (.bin .sub .w64 (.v y) (.imm 2))].reverse ++ st.acc, fresh := st.fresh }) ∨
    (T.known.natSucc ≠ some c ∧ T.known.natZero ≠ some c ∧ ∃ info, Fir.CtorInfo.ofKey T.ctors c = some info ∧
      i < info.arity ∧
      st' = { st with
        acc := [.assign x (.load .w64 .zero (mem y (fieldOffset i)))].reverse ++ st.acc, fresh := st.fresh }) := by
  cases h1 : (T.known.natSucc == some c)
  · cases h2 : (T.known.natZero == some c)
    · cases hk : Fir.CtorInfo.ofKey T.ctors c with
      | none => simp only [Lower.proj, h1, h2, hk, Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
      | some info =>
        by_cases hi : i < info.arity
        · simp only [Lower.proj, h1, h2, hk, hi, Bool.false_eq_true, ↓reduceIte] at h
          have := (assign_run st x (.load .w64 .zero (mem y (fieldOffset i)))).symm.trans h
          simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at this
          exact .inr ⟨by simpa using h1, by simpa using h2, info, rfl, hi, this.symm⟩
        · simp only [Lower.proj, h1, h2, hk, hi, Bool.false_eq_true, ↓reduceIte, StateT.run] at h
          throw_absurd at h
    · simp only [Lower.proj, h1, h2, Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h
  · by_cases hi : i = 0
    · subst hi
      simp only [Lower.proj, h1, ↓reduceIte, BEq.rfl] at h
      have := (assign_run st x (.bin .sub .w64 (.v y) (.imm 2))).symm.trans h
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at this
      exact .inl ⟨by simpa using h1, rfl, this.symm⟩
    · have hi' : (i == 0) = false := by simpa using hi
      simp only [Lower.proj, h1, hi', Bool.false_eq_true, ↓reduceIte, StateT.run] at h; throw_absurd at h

/-! ## The simulations -/

/-- **A projection simulates Cfg's**. -/
theorem proj_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x y : Nat} {c : Key.CtorKey} {i : Nat}
    (hrun : (Lower.proj f T x y c i).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hx : x < sup) (hy : ¬ D y) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st'.cur) st'.acc.length x (.proj y c i) := by
  rcases proj_run hrun with ⟨hs, rfl, rfl⟩ | ⟨hs, hz, info, hk, hi, rfl⟩
  · refine fun P H ρ ρl mem rest v H' hheap hρ hr => ?_
    obtain ⟨rfl, u, fs, hu, hac, hv⟩ := evalRhs_proj hr
    obtain ⟨w, hw, hrel⟩ := hρ.val hu hy
    have hval : ∃ n, u = .lit (.nat (n + 1)) ∧ v = .lit (.nat n) := by
      cases u with
      | lit l =>
        cases l with
        | nat n =>
          cases n with
          | zero =>
            simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
            obtain ⟨_, -, -, rfl⟩ := hac
            simp at hv
          | succ n =>
            simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
            obtain ⟨_, -, -, rfl⟩ := hac
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
            exact ⟨n, rfl, hv.symm⟩
        | str _ => exact absurd hrel id
      | ctor0 c' =>
        simp only [Own.RVal.asCtor, Option.some.injEq, Prod.mk.injEq] at hac
        obtain ⟨-, rfl⟩ := hac
        simp at hv
      | erased => simp [Own.RVal.asCtor] at hac
      | loc ℓ =>
        simp only [Own.RVal.asCtor, Own.Heap.cell?] at hac
        split at hac
        · rename_i rc mode b hcell
          simp only [Option.some.injEq, Prod.mk.injEq] at hac
          obtain ⟨rfl, -⟩ := hac
          exact absurd hs (cell_notNat hheap hrel hcell).2.1
        · simp at hac
    obtain ⟨n, rfl, rfl⟩ := hval
    have hpred := natPred_word hrel
    have hw1 : w ≠ 1 := by
      intro e
      subst e
      have := (natWord_iff.1 hrel).2
      simp at this
    simp only [Nat.add_sub_cancel, hw1, ↓reduceIte] at hpred
    refine .inl ⟨0, ρl.insert x (w - 2), mem, P, straight_star hF hH hC ho (by simp [Lir.Stmt.isCall])
      (by simp only [lir_eval, hw]), hheap, List.prefix_refl _, hρ.insert hx hpred⟩
  · refine fun P H ρ ρl mem rest v H' hheap hρ hr => ?_
    obtain ⟨hHe, u, fs, hu, hac, hv⟩ := evalRhs_proj hr
    rw [hHe]
    obtain ⟨w, hw, hrel⟩ := hρ.val hu hy
    have hcell : ∃ ℓ rc mode b, u = .loc ℓ ∧ H.cells[ℓ]? = some (.live rc mode b) ∧ fs = b.fields := by
      cases u with
      | lit l =>
        cases l with
        | nat n =>
          cases n with
          | zero =>
            simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
            obtain ⟨_, h, rfl, -⟩ := hac
            exact absurd h hz
          | succ n =>
            simp only [Own.RVal.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hac
            obtain ⟨_, h, rfl, -⟩ := hac
            exact absurd h hs
        | str _ => exact absurd hrel id
      | ctor0 c' =>
        simp only [Own.RVal.asCtor, Option.some.injEq, Prod.mk.injEq] at hac
        obtain ⟨-, rfl⟩ := hac
        simp at hv
      | erased => simp [Own.RVal.asCtor] at hac
      | loc ℓ =>
        simp only [Own.RVal.asCtor, Own.Heap.cell?] at hac
        split at hac
        · rename_i rc mode b hcell
          simp only [Option.some.injEq, Prod.mk.injEq] at hac
          exact ⟨ℓ, rc, mode, b, rfl, hcell, hac.2.symm⟩
        · simp at hac
    obtain ⟨ℓ, rc, mode, b, rfl, hcl, rfl⟩ := hcell
    obtain ⟨-, -, hc⟩ := cell_notNat hheap hrel hcl
    obtain ⟨w', hw', hv'⟩ := hc.fields i v hv
    have hload : Lir.Rhs.eval ρl mem ctx (.load .w64 .zero (Lower.mem y (fieldOffset i))) = some w' := by
      rw [fieldOffset_nat]
      exact load_word (eval_mem hw (8 + 8 * i)) hw'
    refine .inl ⟨0, ρl.insert x w', mem, P, straight_star hF hH hC ho (by simp [Lir.Stmt.isCall])
      (by simp only [Lir.execList, Lir.Stmt.exec, hload, Option.bind_eq_bind, Option.bind_some]), hheap,
      List.prefix_refl _, hρ.insert hx hv'⟩

/-- **A copy simulates Cfg's**. -/
theorem arg_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st : St} {x : Nat} {a : Fir.Arg} {la : Lir.Arg}
    (hC : Ext C { st with acc := [Lir.Stmt.assign x (.arg la)].reverse ++ st.acc, fresh := st.fresh }) (ho : Open st)
    (hx : x < sup) (hop : operand f a = .ok (some la)) (hlive : LiveArg D a) :
    RhsSim T lp ctx D sup fn (off + st.cur) st.acc.length (off + st.cur)
      ([Lir.Stmt.assign x (.arg la)].reverse ++ st.acc).length x (.fir (.arg a)) := by
  apply straight_sim hF hH hC ho (by simp [Lir.Stmt.isCall])
  intro P H ρ ρl mem v H' hρ hr
  obtain ⟨rfl, hv⟩ := evalRhs_arg hr
  obtain ⟨w, hw, hrel, -⟩ := operand_rel hρ hop hlive hv
  exact ⟨rfl, ρl.insert x w, by simp only [lir_eval, hw], hρ.insert hx hrel⟩

end IxCC.Rt.Proof
