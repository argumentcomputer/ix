import Compilatrix.Own.Plain.Proof.Values
import Compilatrix.Own.Plain.Proof.Actions
import Compilatrix.Own.Plain.Proof.Unfold

/-! Projection obtains a borrowed child from an actual constructor view,
then establishes its owned result with the canonical increment. This includes
Nat-successor views whose child is an immediate rather than a heap edge. -/

set_option autoImplicit false

namespace Compilatrix.Own.Plain

open Rc
open Compilatrix.Sem (Result)

theorem asCtor_field_canDup {H : Heap} {external : Nat → Nat} {roots : List RVal}
    {K : Lam.Known} {parent v : RVal} {key : Key.CtorKey} {fields : List RVal}
    (hb : Balance H external roots) (hc : parent.asCtor K H = some (key, fields))
    (hm : v ∈ fields) : CanDup H v := by
  cases parent with
  | loc l =>
    cases hl : H.cell? l with
    | none => simp [RVal.asCtor, hl] at hc
    | some cell =>
      cases cell with
      | dead => simp [RVal.asCtor, hl] at hc
      | live rc m b =>
        have he : b.ctor.key = key ∧ b.fields = fields := by
          simpa [RVal.asCtor, hl] using hc
        rw [← he.2] at hm
        exact canDup_field hb hl hm
  | lit lit =>
    cases lit with
    | str s => simp [RVal.asCtor] at hc
    | nat n =>
      cases n with
      | zero =>
        cases hk : K.natZero <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        simp at hm
      | succ n =>
        cases hk : K.natSucc <;> simp [RVal.asCtor, hk] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have he : v = .lit (.nat n) := by simpa using hm
        subst v
        trivial
  | ctor0 c =>
    have he : c.key = key ∧ [] = fields := by simpa [RVal.asCtor] using hc
    rw [← he.2] at hm
    simp at hm
  | erased => simp [RVal.asCtor] at hc

theorem projection_owned (P : Program) (k : Nat) (ρ : Own.Env) (J : List JEntry)
    (H : Heap) (x y : Fir.Var) (key : Key.CtorKey) (i : Nat) (c : Code)
    {external : Nat → Nat} {roots : List RVal} {parent : RVal} {source : Fir.Val}
    {fields : List Fir.Val} {w : Fir.Val}
    (hb : Balance H external roots) (hy : ρ.get? y = some parent)
    (hd : Proof.Den H parent source)
    (hc : source.asCtor P.source.known = some (key, fields)) (hi : fields[i]? = some w) :
    ∃ v H',
      eval P k ρ J H (.bind x (.proj y key i) (.act (.inc x 1) c)) =
        eval P k (ρ.insert x v) J H' c ∧
      Balance H' external (v :: roots) ∧ Proof.Den H' v w ∧
      ∀ root, H.value? root = H'.value? root := by
  obtain ⟨vs, hview, hfields⟩ := (Values.asCtor_den P.source.known hd).1 key fields hc
  obtain ⟨v, hget, hv⟩ := hfields.get' hi
  have hm : v ∈ vs := List.mem_of_getElem? hget
  obtain ⟨H', hinc, hb', hvalues⟩ := inc_root hb (asCtor_field_canDup hb hview hm)
  refine ⟨v, H', ?_, hb', ?_, hvalues⟩
  · rw [eval_bindRhs P k ρ J H x (.proj y key i) (.act (.inc x 1) c)
      (by intro f args h; cases h)]
    have hr : evalRhs P.tables ρ H (.proj y key i) = .ok (v, H) := by
      simp [evalRhs, Own.evalRhs, hy, Program.tables, hview, hget, Result.ofOption, Result.map]
    rw [hr]
    simp only [Result.bind_ok]
    rw [eval_act]
    simp [evalAction, Src.NatMap.get?_insert_self, hinc, Result.ofOption, Result.bind]
  · change H'.value? v = some w
    rw [← hvalues v]
    exact hv


end Compilatrix.Own.Plain
