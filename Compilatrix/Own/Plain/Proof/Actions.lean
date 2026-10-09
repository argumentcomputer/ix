import Compilatrix.Own.Plain.Semantics
import Compilatrix.Own.Rc.Proof.Allocation
import Compilatrix.Own.Rc.Proof.Transfer

/-! Concrete action/heap interfaces for canonical transfer refinement. Every
operation below uses the actual Plain evaluator and environment lookup. The
premises describe ownership and denotations, never a simulated execution. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

theorem canDup_member {H : Heap} {external : Nat → Nat} {roots : List RVal} {v : RVal}
    (hb : Balance H external roots) (hm : v ∈ roots) : CanDup H v := by
  cases v with
  | loc l =>
    have hp := refsIn_pos hm
    have h := hb l
    change 0 < dynCount H l
    omega
  | lit _ | ctor0 _ | erased => trivial

theorem evalAction_inc_owned {ρ : Own.Env} {H : Heap} {external : Nat → Nat}
    {roots : List RVal} {x : Fir.Var} {v : RVal}
    (hx : ρ.get? x = some v) (hb : Balance H external roots) (hm : v ∈ roots) :
    ∃ H', evalAction ρ H (.inc x 1) = .ok H' ∧ Balance H' external (v :: roots) ∧
      ∀ root, H.value? root = H'.value? root := by
  obtain ⟨H', hi, hb', hv⟩ := inc_root hb (canDup_member hb hm)
  exact ⟨H', by simp [evalAction, hx, hi, Result.ofOption], hb', hv⟩

/-- A newly projected variable borrows an existing field until its explicit
increment. Its permission follows from the live incoming edge. -/
theorem evalAction_inc_field {ρ : Own.Env} {H : Heap} {external : Nat → Nat}
    {roots : List RVal} {x parent rc : Nat} {m : OMode} {b : Body} {v : RVal}
    (hx : ρ.get? x = some v) (hb : Balance H external roots)
    (hc : H.cell? parent = some (.live rc m b)) (hm : v ∈ b.fields) :
    ∃ H', evalAction ρ H (.inc x 1) = .ok H' ∧ Balance H' external (v :: roots) ∧
      ∀ root, H.value? root = H'.value? root := by
  obtain ⟨H', hi, hb', hv⟩ := dup_projection hb hc hm
  exact ⟨H', by simp [evalAction, hx, hi, Result.ofOption], hb', hv⟩

theorem evalAction_dec_owned {ρ : Own.Env} {H : Heap} {external : Nat → Nat}
    {held : List RVal} {x : Fir.Var} {v : RVal}
    (hx : ρ.get? x = some v) (hb : Balance H external (v :: held)) :
    ∃ H', evalAction ρ H (.dec x) = .ok H' ∧ Balance H' external held ∧
      (∀ root, root ∈ held → H.value? root = H'.value? root) ∧
      (∀ root, ExternalRoot external root → H.value? root = H'.value? root) := by
  obtain ⟨H', hd, hb', hv, he⟩ := dropAll_retaining H [v] held hb
  exact ⟨H', by simp [evalAction, hx, hd, Result.ofOption], hb', hv, he⟩

theorem evalRhs_alloc_owned {T : Own.Tables} {ρ : Own.Env} {H : Heap}
    {external : Nat → Nat} {c : Fir.CtorInfo} {args : List Fir.Arg}
    {fields : List RVal} {values : List Fir.Val}
    (ha : Own.evalArgs ρ args = some fields) (hn : fields.length = c.arity)
    (hp : 0 < c.arity) (hb : Balance H external fields)
    (hv : Sem.Forall2 (Proof.Den H) fields values) :
    let allocated := H.alloc .rc { ctor := c, fields }
    evalRhs T ρ H (.ctor c args) = .ok allocated ∧
      Balance allocated.2 external [allocated.1] ∧
      Proof.Den allocated.2 allocated.1 (.ctor c values) ∧
      ∀ v w, Proof.Den H v w → Proof.Den allocated.2 v w := by
  refine ⟨?_, alloc_sound hb hv⟩
  have hz : c.arity ≠ 0 := by omega
  simp [evalRhs, Own.evalRhs, ha, hn, Fir.CtorInfo.fieldless, hz]


end Compilatrix.Own.Plain
