import Compilatrix.Cfg.Rc.Semantics
import Compilatrix.Cfg.Rc.Proof.Markers
import Compilatrix.Own.Plain.Proof.Prefixes
import Compilatrix.Sem.Smallstep

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Sem (Result Star)
open Compilatrix.Own (RVal Heap)

theorem step_marker {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Heap}
    {slot : Nat} {a : Action} {rest : List Instr} {table : ActionTable}
    (hr : fr.rest = marker P.base.size slot a :: rest)
    (ht : P.actions.get? fr.fn = some table) (ha : table.get? slot = some a) :
    step P (.run fr stk H) = actionStep fr stk H rest a := by
  simp only [step, hr, reserved_marker, ↓reduceIte, decode_marker, ht, ha]

theorem step_checked_head {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Heap}
    {i : Instr} {rest : List Instr} {table : ActionTable} {first : Nat}
    (hr : fr.rest = i :: rest) (ht : P.actions.get? fr.fn = some table)
    (hc : checkMarkers P.base.size first (i :: rest) table = true)
    (reservedHead : reserved P.base.size i = true) :
    ∃ slot a, decode P.base.size i = some (slot, a) ∧ first ≤ slot ∧
      step P (.run fr stk H) = actionStep fr stk H rest a := by
  obtain ⟨slot, a, hd, hs, ha⟩ := checked_head_intercepts hc reservedHead
  refine ⟨slot, a, hd, hs, ?_⟩
  simp only [step, hr, reservedHead, ↓reduceIte, hd, ht, ha]

theorem step_missing_table {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Heap}
    {slot : Nat} {a : Action} {rest : List Instr}
    (hr : fr.rest = marker P.base.size slot a :: rest)
    (ht : P.actions.get? fr.fn = none) : step P (.run fr stk H) = .stuck := by
  simp only [step, hr, reserved_marker, ↓reduceIte, decode_marker, ht]

theorem step_missing_entry {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Heap}
    {slot : Nat} {a : Action} {rest : List Instr} {table : ActionTable}
    (hr : fr.rest = marker P.base.size slot a :: rest)
    (ht : P.actions.get? fr.fn = some table) (ha : table.get? slot = none) :
    step P (.run fr stk H) = .stuck := by
  simp only [step, hr, reserved_marker, ↓reduceIte, decode_marker, ht, ha]

theorem step_action_success {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H H' : Heap}
    {slot : Nat} {a : Action} {rest : List Instr} {table : ActionTable}
    (hr : fr.rest = marker P.base.size slot a :: rest)
    (ht : P.actions.get? fr.fn = some table) (ha : table.get? slot = some a)
    (he : Own.Plain.evalAction fr.env H a = .ok H') :
    step P (.run fr stk H) = .next (.run { fr with rest } stk H') false := by
  rw [step_marker hr ht ha]
  simp only [actionStep, he]

theorem step_ordinary {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Heap}
    {i : Instr} {rest : List Instr} (hr : fr.rest = i :: rest)
    (ho : reserved P.base.size i = false) :
    step P (.run fr stk H) = Cfg.step .rc P.base (.run fr stk H) := by
  simp only [step, hr, ho, Bool.false_eq_true, ↓reduceIte]

end Compilatrix.Cfg.Rc
