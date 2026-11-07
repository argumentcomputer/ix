import IxCC.Cfg.Rc.Proof.Names
import IxCC.Cfg.Rc.Proof.Environment

/-! Real lexical environments and existing block-layout witnesses, with a
separate marker-slot supply for every saved join body. Dummy marker bindings
do not appear in any source environment or advance its real-name bound. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc
open Cfg.Lower (JScope)
open Cfg.Proof (Blocks Impl Below)

inductive Joins (limit : Nat) (B : Blocks) (self : Fir.FunId) (ρc : Own.Env) :
    Nat → JScope → List Own.Plain.JEntry → Prop
  | nil {lo : Nat} : Joins limit B self ρc lo [] []
  | cons {lo loEntry loBody first : Nat} {bj : BlockId} {Jc : JScope}
      {e : Own.Plain.JEntry} {rest : List Own.Plain.JEntry} {ps : List (Fir.Var × Own.PSig)} :
      Joins limit B self ρc loEntry Jc rest → loEntry ≤ lo → e.params = ps.map (·.1) →
      (e.charged = true → e.isRec = true) →
      Impl B self (if e.isRec then (e.id, bj, true) :: Jc else Jc) bj ps [] (bj + 1)
        (skeleton limit first e.body) →
      EnvSub e.env ρc → Below loEntry e.env → (∀ p ∈ ps, loEntry ≤ p.1) →
      loEntry ≤ loBody → (∀ p ∈ ps, p.1 < loBody) → names loBody e.body = true →
      Joins limit B self ρc lo ((e.id, bj, e.charged) :: Jc) (e :: rest)

namespace Joins
variable {limit : Nat} {B : Blocks} {self : Fir.FunId}

theorem mono {ρ : Own.Env} {lo next : Nat} {Jc : JScope} {J : List Own.Plain.JEntry}
    (h : Joins limit B self ρ lo Jc J) (hle : lo ≤ next) : Joins limit B self ρ next Jc J := by
  cases h with
  | nil => exact .nil
  | cons tail bound params charge impl sub below ps lower upper scopedNames =>
    exact .cons tail (Nat.le_trans bound hle) params charge impl sub below ps lower upper scopedNames

theorem agree {ρ target : Own.Env} {lo : Nat} {Jc : JScope} {J : List Own.Plain.JEntry}
    (h : Joins limit B self ρ lo Jc J)
    (eq : ∀ x, x < lo → target.get? x = ρ.get? x) : Joins limit B self target lo Jc J := by
  induction h with
  | nil => exact .nil
  | @cons lo loEntry loBody first bj Jc e rest ps tail bound params charge impl sub below psLower lower upper scopedNames ih =>
    refine .cons (ih fun x hx => eq x (Nat.lt_of_lt_of_le hx bound)) bound params charge impl
      (fun x v hx => ?_) below psLower lower upper scopedNames
    rw [eq x (Nat.lt_of_lt_of_le (below x v hx) bound)]
    exact sub x v hx

theorem lookup {ρ : Own.Env} {lo : Nat} {Jc : JScope} {J : List Own.Plain.JEntry}
    (h : Joins limit B self ρ lo Jc J) {j : Fir.JoinId} {e : Own.Plain.JEntry}
    {rest : List Own.Plain.JEntry} (found : Own.Plain.lookupJ j J = some (e, rest)) :
    ∃ bj Jc' ps loEntry loBody first,
      Jc.lookup j = some (bj, e.charged) ∧ e.id = j ∧ Joins limit B self ρ loEntry Jc' rest ∧
      loEntry ≤ lo ∧ e.params = ps.map (·.1) ∧ (e.charged = true → e.isRec = true) ∧
      Impl B self (if e.isRec then (e.id, bj, true) :: Jc' else Jc') bj ps [] (bj + 1)
        (skeleton limit first e.body) ∧
      EnvSub e.env ρ ∧ Below loEntry e.env ∧ (∀ p ∈ ps, loEntry ≤ p.1) ∧
      loEntry ≤ loBody ∧ (∀ p ∈ ps, p.1 < loBody) ∧ names loBody e.body = true := by
  induction h generalizing e rest with
  | nil => simp [Own.Plain.lookupJ] at found
  | @cons lo loEntry loBody first bj Jc saved tail ps previous bound params charge impl sub below psLower lower upper scopedNames ih =>
    simp only [Own.Plain.lookupJ] at found
    split at found
    · next idEq =>
      simp only [Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      refine ⟨bj, Jc, ps, loEntry, loBody, first, ?_, idEq, previous, bound, params,
        charge, impl, sub, below, psLower, lower, upper, scopedNames⟩
      simp [List.lookup, idEq]
    · next idNe =>
      obtain ⟨b, js, qs, low, high, start, lookup, idEq, previous', bound', params',
        charge', impl', sub', below', psLower', lower', upper', scopedNames'⟩ := ih found
      refine ⟨b, js, qs, low, high, start, ?_, idEq, previous', Nat.le_trans bound' bound,
        params', charge', impl', sub', below', psLower', lower', upper', scopedNames'⟩
      have different : (j == saved.id) = false := by simpa using fun h => idNe h.symm
      simp [List.lookup, different, lookup]
end Joins


end IxCC.Cfg.Rc
