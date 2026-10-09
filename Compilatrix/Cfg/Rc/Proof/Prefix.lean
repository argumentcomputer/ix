import Compilatrix.Cfg.Rc.Prefix
import Compilatrix.Cfg.Rc.Proof.Step

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Sem (Result Star)
open Compilatrix.Own (Heap)

theorem prefixTable_below (first : Nat) (as : List Action) {slot : Nat} (hs : slot < first) :
    (prefixTable first as).get? slot = none := by
  induction as generalizing first with
  | nil => rfl
  | cons a as ih =>
    simp only [prefixTable, Src.NatMap.get?_insert_ne _ _ (by omega : slot ≠ first)]
    exact ih _ (by omega)

theorem collect_prefix_from (limit lower first : Nat) (hl : lower ≤ first) (as : List Action) :
    collect limit lower (encodePrefix limit first as) = some (prefixTable first as) := by
  induction as generalizing first with
  | nil => rfl
  | cons a as ih =>
    have absent : (prefixTable (first + 1) as).contains first = false := by
      simp only [Src.NatMap.contains, prefixTable_below _ _ (by omega : first < first + 1)]
      rfl
    have tailCollect := ih (first + 1) (by omega)
    have fresh : ¬ first < lower := by omega
    simp [encodePrefix, collect, reserved_marker, decode_marker, tailCollect, absent, prefixTable, fresh]

theorem collect_prefix (limit first : Nat) (as : List Action) :
    collect limit first (encodePrefix limit first as) = some (prefixTable first as) :=
  collect_prefix_from limit first first (by omega) as

theorem checkMarkers_prefix (limit first : Nat) (as : List Action) :
    checkMarkers limit first (encodePrefix limit first as) (prefixTable first as) = true :=
  (checkMarkers_iff ..).mpr (collect_prefix limit first as)

def Slots (table : ActionTable) (first : Nat) (as : List Action) : Prop :=
  ∀ n a, as[n]? = some a → table.get? (first + n) = some a

theorem prefixTable_slots (first : Nat) (as : List Action) : Slots (prefixTable first as) first as := by
  intro n a hn
  induction as generalizing first n with
  | nil => simp at hn
  | cons head rest ih =>
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst a
      simp only [prefixTable, Nat.add_zero, Src.NatMap.get?_insert_self]
    | succ n =>
      have hneq : first + (n + 1) ≠ first := by omega
      simp only [prefixTable, Src.NatMap.get?_insert_ne _ _ hneq]
      have he : first + (n + 1) = (first + 1) + n := by omega
      rw [he]
      exact ih _ _ hn

theorem prefix_reach {P : Program} (first : Nat) (as : List Action)
    {fr : Frame} {stk : List (Frame × Fir.Var)} {H H' : Heap} {rest : List Instr} {table : ActionTable}
    (hr : fr.rest = encodePrefix P.base.size first as ++ rest)
    (ht : P.actions.get? fr.fn = some table) (slots : Slots table first as)
    (run : Own.Plain.evalActions fr.env H as = .ok H') :
    Star (step P) (.run fr stk H) 0 (.run { fr with rest } stk H') := by
  induction as generalizing first fr H with
  | nil =>
    simp only [encodePrefix, List.nil_append] at hr
    simp only [Own.Plain.evalActions, Result.ok.injEq] at run
    subst H'
    have he : { fr with rest := rest } = fr := by cases fr; simp_all
    rw [he]
    exact .refl _
  | cons a as ih =>
    cases he : Own.Plain.evalAction fr.env H a with
    | ok H₁ =>
      have runTail : Own.Plain.evalActions fr.env H₁ as = .ok H' := by
        simpa only [Own.Plain.evalActions, he, Result.bind_ok] using run
      have hhead : table.get? first = some a := by simpa using slots 0 a rfl
      have htail : Slots table (first + 1) as := by
        intro n action hn
        have hs := slots (n + 1) action hn
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      have start : fr.rest = marker P.base.size first a ::
          (encodePrefix P.base.size (first + 1) as ++ rest) := by
        simpa only [encodePrefix, List.cons_append] using hr
      apply Star.free (step_action_success start ht hhead he)
      exact ih (first + 1) rfl ht htail runTail
    | timeout | resource _ | trap | stuck =>
      simp [Own.Plain.evalActions, he, Result.bind] at run

end Compilatrix.Cfg.Rc
