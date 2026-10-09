import Compilatrix.Own.Plain.Proof.ShapeOps

set_option autoImplicit false
namespace Compilatrix.Own.Plain
open Rc
open Compilatrix.Sem (Result)

theorem asCtor_bounded {H : Heap} (hh : HeapOk H) (K : Lam.Known)
    {v : RVal} {key : Key.CtorKey} {fields : List RVal}
    (hc : v.asCtor K H = some (key, fields)) : ValuesBounded H.size fields := by
  cases v with
  | loc l =>
    simp only [RVal.asCtor] at hc
    split at hc
    · next rc mode body lookup =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rcases hc with ⟨rfl, rfl⟩
      intro v hv
      cases v with
      | loc k => exact Nat.lt_trans ((hh l rc mode body lookup).2.2.2.2 k hv) (Proof.cell?_some lookup)
      | _ => trivial
    · cases hc
  | ctor0 c =>
    simp only [RVal.asCtor, Option.some.injEq, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩
    simp [ValuesBounded]
  | erased => cases hc
  | lit l =>
    cases l with
    | str s => cases hc
    | nat n =>
      cases n with
      | zero => cases hz : K.natZero <;> simp_all [RVal.asCtor, ValuesBounded]
      | succ n =>
        cases hs : K.natSucc <;> simp_all [RVal.asCtor, ValuesBounded, Bounded]
        rw [← hc.2]
        simp

theorem prim_bounded (T : Own.Tables) (n : Nat) {op : Lam.Prim} {args : List RVal} {v : RVal}
    (hop : Own.primResult T op args = .ok v) : Bounded n v := by
  cases hn : Own.natArgs args with
  | none => simp [Own.primResult, hn] at hop
  | some ns =>
    cases hp : op.sem ns with
    | none => simp [Own.primResult, hn, hp] at hop
    | some result =>
      cases result with
      | nat value => simp [Own.primResult, hn, hp] at hop; subst v; trivial
      | bool b =>
        cases hk : (if b then T.known.boolTrue else T.known.boolFalse) with
        | none => simp [Own.primResult, hn, hp, hk] at hop
        | some key =>
          cases hi : Fir.CtorInfo.ofKey T.ctors key with
          | none => simp [Own.primResult, hn, hp, hk, Own.ctor0Of, hi, Result.ofOption] at hop
          | some info =>
            cases hz : info.fieldless <;>
              simp [Own.primResult, hn, hp, hk, Own.ctor0Of, hi, hz, Result.ofOption] at hop
            subst v
            trivial

theorem rhs_shape {H H' : Heap} {ρ : Own.Env} {T : Own.Tables} {rhs : Fir.Rhs} {v : RVal}
    (hh : HeapOk H) (henv : EnvBounded H.size ρ) (hop : evalRhs T ρ H rhs = .ok (v, H')) :
    HeapOk H' ∧ H.size ≤ H'.size ∧ Bounded H'.size v := by
  cases rhs with
  | arg a =>
    cases ha : Own.evalArg ρ a with
    | none => simp [evalRhs, Own.evalRhs, ha] at hop
    | some w =>
      simp only [evalRhs, Own.evalRhs, ha, Result.ok.injEq, Prod.mk.injEq] at hop
      rcases hop with ⟨rfl, rfl⟩
      exact ⟨hh, Nat.le_refl _, henv.arg ha⟩
  | ctor c args =>
    cases ha : Own.evalArgs ρ args with
    | none => simp [evalRhs, Own.evalRhs, ha] at hop
    | some fields =>
      by_cases hl : fields.length = c.arity
      · cases hz : c.fieldless with
        | true =>
          simp only [evalRhs, Own.evalRhs, ha, hl, hz, ↓reduceIte, Result.ok.injEq, Prod.mk.injEq] at hop
          rcases hop with ⟨rfl, rfl⟩
          exact ⟨hh, Nat.le_refl _, trivial⟩
        | false =>
          simp only [evalRhs, Own.evalRhs, ha, hl, hz, ↓reduceIte, Bool.false_eq_true,
            Result.ok.injEq] at hop
          have hp : 0 < c.arity := by simp only [Fir.CtorInfo.fieldless, beq_eq_false_iff_ne] at hz; omega
          have hbody : BodyOk H.size { ctor := c, fields } :=
            ⟨hl, hp, fun l hmem => henv.args args ha (.loc l) hmem⟩
          have hshape := heapOk_alloc hh hbody
          have hsize := Proof.alloc_size .rc H { ctor := c, fields }
          cases hop
          exact ⟨hshape, by simp [Heap.size], by simpa [Heap.alloc, Heap.size, Bounded]⟩
      · simp [evalRhs, Own.evalRhs, ha, hl] at hop
  | prim op args =>
    cases ha : Own.evalArgs ρ args with
    | none => simp [evalRhs, Own.evalRhs, ha] at hop
    | some values =>
      cases hp : Own.primResult T op values with
      | ok w =>
        simp only [evalRhs, Own.evalRhs, ha, hp, Result.map, Result.bind,
          Result.ok.injEq, Prod.mk.injEq] at hop
        rcases hop with ⟨rfl, rfl⟩
        exact ⟨hh, Nat.le_refl _, prim_bounded T H.size hp⟩
      | timeout | resource _ | trap | stuck =>
        simp [evalRhs, Own.evalRhs, ha, hp, Result.map, Result.bind] at hop
  | proj x key i =>
    cases hx : ρ.get? x with
    | none => simp [evalRhs, Own.evalRhs, hx] at hop
    | some value =>
      cases hc : value.asCtor T.known H with
      | none => simp [evalRhs, Own.evalRhs, hx, hc] at hop
      | some pair =>
        obtain ⟨key', fields⟩ := pair
        by_cases hk : key' = key
        · cases hf : fields[i]? with
          | none => simp [evalRhs, Own.evalRhs, hx, hc, hk, hf, Result.ofOption, Result.map, Result.bind] at hop
          | some field =>
            simp only [evalRhs, Own.evalRhs, hx, hc, hk, ↓reduceIte, hf, Result.ofOption,
              Result.map, Result.bind, Result.ok.injEq, Prod.mk.injEq] at hop
            rcases hop with ⟨rfl, rfl⟩
            exact ⟨hh, Nat.le_refl _, asCtor_bounded hh T.known hc field (List.mem_of_getElem? hf)⟩
        · simp [evalRhs, Own.evalRhs, hx, hc, hk] at hop
  | call f args => simp [evalRhs, Own.evalRhs] at hop

end Compilatrix.Own.Plain
