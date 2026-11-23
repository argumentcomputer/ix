import IxCC.Cfg.Rc.Semantics
import IxCC.Cfg.Rc.Proof.Markers
import IxCC.Own.Plain.Proof.Prefixes
import IxCC.Sem.Smallstep

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Sem (Result Star)
open IxCC.Own (RVal Heap)

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
    (ho : reserved P.base.size i = false)
    (hnr : isReuseOp P.base.size i = false) :
    step P (.run fr stk H) = Cfg.step .rc P.base (.run fr stk H) := by
  simp only [step, hr, ho, hnr, Bool.false_eq_true, ↓reduceIte]

theorem step_reset {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H H' : Heap}
    {slotReg x ctorIdx mask : Nat} {uniq : Bool} {rest : List Instr}
    {ctor : Fir.CtorInfo} {sv : RVal}
    (hr : fr.rest = resetMarker P.base.size slotReg x ctorIdx mask uniq :: rest)
    (hctor : heapCtorAt P.base.ctors ctorIdx = some ctor)
    (he : Own.Plain.evalResetMask fr.env H x ctor mask uniq = .ok (sv, H')) :
    step P (.run fr stk H) = .next (.run { fr with rest, env := fr.env.insert slotReg sv } stk H') false := by
  simp only [step, hr, reserved_resetMarker, isReuseOp_resetMarker, Bool.false_eq_true, ↓reduceIte,
    decodeReset_resetMarker, decodeReuse_resetMarker, hctor, he]

theorem step_reuse {P : Program} {fr : Frame} {stk : List (Frame × Fir.Var)} {H H' : Heap}
    {dst slotReg ctorIdx : Nat} {uniq : Bool} {args : List Fir.Arg} {rest : List Instr}
    {ctor : Fir.CtorInfo} {sv v : RVal}
    (hr : fr.rest = reuseMarker P.base.size dst slotReg ctorIdx uniq args :: rest)
    (hctor : heapCtorAt P.base.ctors ctorIdx = some ctor)
    (hsv : fr.env.get? slotReg = some sv)
    (he : Own.Plain.evalReuseVal fr.env H sv ctor args uniq = .ok (v, H')) :
    step P (.run fr stk H) = .next (.run { fr with rest, env := fr.env.insert dst v } stk H') false := by
  simp only [step, hr, reserved_reuseMarker, isReuseOp_reuseMarker, Bool.false_eq_true, ↓reduceIte,
    decodeReset_reuseMarker, decodeReuse_reuseMarker, hctor, hsv, he]

end IxCC.Cfg.Rc
