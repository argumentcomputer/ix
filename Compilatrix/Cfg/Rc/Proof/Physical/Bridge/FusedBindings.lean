import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.FusedWords

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Rt.Rc.Procs
open Compilatrix.Rt.Proof (ListRel)

/-- Actual parameter binding keeps the dynamic-address relation. Parameters
are processed in evaluator order, so repeated names retain the last binding;
no distinctness or heap-execution assumption is required. -/
theorem FusedWords.bindParams
    {addresses : AddressMap} {D : Nat → Prop} {bound : Nat} :
    ∀ {params : List Nat} {values : List Own.RVal} {words : List Lir.Word}
      {source : Own.Env} {target : Lir.Env},
      FusedWords addresses D bound source target →
      ListRel (fun value word => valueWord addresses value = some word) values words →
      params.length = values.length → (∀ x ∈ params, x < bound) →
      ∃ after, Lir.bindParams target params words = some after ∧
        FusedWords addresses D bound (Own.bindAll source params values) after
  | [], [], [], _, _, related, _, _, _ => ⟨_, rfl, related⟩
  | x :: params, value :: values, word :: words, _, _, related, .cons represented tail,
      length, real => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at length
    obtain ⟨after, binding, words⟩ := FusedWords.bindParams
      (related.bind (real x (by simp)) represented) tail length
      (fun y member => real y (by simp [member]))
    exact ⟨after, binding, words⟩
  | [], _ :: _, _, _, _, _, _, length, _ => by simp at length
  | _ :: _, [], _, _, _, _, _, length, _ => by simp at length

/-- The same theorem at function entry derives the real target binding from
empty maps. Omitted comparison names may occur among parameters as well. -/
theorem FusedWords.entry
    {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    (params : List Nat) {values : List Own.RVal} {words : List Lir.Word}
    (represented : ListRel (fun value word => valueWord addresses value = some word) values words)
    (length : params.length = values.length) (real : ∀ x ∈ params, x < bound) :
    ∃ target, Lir.bindParams ({} : Lir.Env) params words = some target ∧
      FusedWords addresses D bound (Own.bindAll .leaf params values) target :=
  FusedWords.bindParams FusedWords.empty represented length real

/-- Use an already selected concrete target environment without changing the
evaluation order or assuming another parameter-binding convention. -/
theorem FusedWords.boundParams
    {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    {source : Own.Env} {target after : Lir.Env}
    (related : FusedWords addresses D bound source target)
    {params : List Nat} {values : List Own.RVal} {words : List Lir.Word}
    (represented : ListRel (fun value word => valueWord addresses value = some word) values words)
    (length : params.length = values.length) (real : ∀ x ∈ params, x < bound)
    (binding : Lir.bindParams target params words = some after) :
    FusedWords addresses D bound (Own.bindAll source params values) after := by
  obtain ⟨actual, actualBinding, relation⟩ := related.bindParams represented length real
  have equal : actual = after := Option.some.inj (actualBinding.symm.trans binding)
  exact equal ▸ relation




end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
