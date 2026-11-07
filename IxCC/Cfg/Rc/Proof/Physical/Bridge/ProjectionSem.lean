import IxCC.Cfg.Rc.Proof.Physical.Bridge.ScalarPure
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorValues
import IxCC.Cfg.Rc.Proof.Physical.Bridge.Projection

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Lower
open IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Src (NatMap)

/-- Both actual projection expansions use the dynamic heap relation. Nat
successor subtraction is selected by the real table pin; object projection
reads the selected field directly and derives its header facts from LiveCell. -/
theorem projection_sim {T : Tables} {f : Fir.FunId} {lp : Lir.Program} {ctx : Word} {D : Nat → Prop} {sup : Nat}
    {fn : Nat} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock} (hF : lp.funcs[fn]? = some F)
    (hH : Holds f F off starts C) {st st' : St} {x y : Nat} {c : Key.CtorKey} {i : Nat}
    (hrun : (Lower.proj f T x y c i).run st = .ok ((), st')) (hC : Ext C st') (ho : Open st)
    (hx : x < sup) (hy : ¬ D y)
    {P : AddressMap} {H H' : Own.Heap} {ρ : Own.Env} {ρl : Lir.Env} {mem : X86.Memory}
    (rest : List Lir.Frame) {v : Own.RVal}
    (physical : HeapLive H P mem) (compatible : HeapCtorOk T H)
    (hρ : EnvRel T P D sup ρ ρl)
    (hr : Own.evalRhs .rc (ownTables T) ρ H (.proj y c i) = .ok (v, H')) :
    H' = H ∧ ∃ after, Sem.Star (Lir.semStep lp)
      (Lir.atState mem ctx fn (off + st.cur) st.acc.length ρl rest) 0
      (Lir.atState mem ctx fn (off + st'.cur) st'.acc.length after rest) ∧
      EnvRel T P D sup (ρ.insert x v) after := by
  rcases proj_run hrun with ⟨hs, rfl, rfl⟩ | ⟨hs, hz, info, hk, hi, rfl⟩
  · obtain ⟨rfl, u, fs, hu, hac, hv⟩ := evalRhs_proj hr
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
          have notNat := (compatible ℓ rc mode b hcell).1.notNat
          simp only [isNatKey, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at notNat
          exact absurd hs notNat.2
        · simp at hac
    obtain ⟨n, rfl, rfl⟩ := hval
    have hpred := natPred_word hrel
    have hw1 : w ≠ 1 := by
      intro e
      subst e
      have := (natWord_iff.1 hrel).2
      simp at this
    simp only [Nat.add_sub_cancel, hw1, ↓reduceIte] at hpred
    exact ⟨rfl, ρl.insert x (w - 2), straight_star hF hH hC ho (by simp [Lir.Stmt.isCall])
      (by simp only [lir_eval, hw]), hρ.insert hx hpred⟩
  · obtain ⟨hHe, u, fs, hu, hac, hv⟩ := evalRhs_proj hr
    subst H'
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
    obtain ⟨_, address, mapped, hc⟩ := physical.cell ℓ rc mode b hcl
    have equal : w = address := Option.some.inj (hrel.symm.trans mapped)
    subst address
    obtain ⟨w', represented, bytes⟩ := hc.fields i v hv
    have hv' : ValRel T P v w' := ValRel.of_words represented
      ((compatible ℓ rc mode b hcl).2.2 v (List.mem_of_getElem? hv))
    have hload : Lir.Rhs.eval ρl mem ctx (.load .w64 .zero (Lower.mem y (fieldOffset i))) = some w' := by
      rw [fieldOffset_nat]
      have addressEval := eval_mem (ctx := ctx) hw (8 + 8 * i)
      simp only [Lir.Rhs.eval, addressEval, Option.bind_eq_bind, Option.bind_some, Lir.loadWord, bytes.read64]
    exact ⟨rfl, ρl.insert x w', straight_star hF hH hC ho (by simp [Lir.Stmt.isCall])
      (by simp only [Lir.execList, Lir.Stmt.exec, hload, Option.bind_eq_bind, Option.bind_some]),
      hρ.insert hx hv'⟩



end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
