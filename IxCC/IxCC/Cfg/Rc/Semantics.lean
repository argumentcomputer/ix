import IxCC.Cfg.Rc.Syntax
import IxCC.Cfg.Semantics
import IxCC.Own.Plain.Semantics

set_option autoImplicit false
namespace IxCC.Cfg.Rc
open IxCC.Own (RVal Heap)

def actionStep (fr : Frame) (stk : List (Frame × Fir.Var)) (H : Heap) (rest : List Instr) (a : Action) :
    Sem.Step State (RVal × Heap) :=
  match Own.Plain.evalAction fr.env H a with
  | .ok H' => .next (.run { fr with rest } stk H') false
  | .resource r => .fail r
  | .trap => .trap
  | .timeout | .stuck => .stuck

def heapCtorAt (ctors : List Lam.CtorInfo) (idx : Nat) : Option Fir.CtorInfo := do
  let c ← (ctors.filter (fun c => c.arity > 0))[idx]?
  Fir.CtorInfo.ofKey ctors c.key

def step (P : Program) (s : State) : Sem.Step State (RVal × Heap) :=
  match s with
  | .run fr stk H =>
    match fr.rest with
    | i :: rest =>
      if reserved P.base.size i then
        match decode P.base.size i, P.actions.get? fr.fn with
        | some (slot, a), some table =>
          match table.get? slot with
          | some stored => if stored = a then actionStep fr stk H rest a else .stuck
          | none => .stuck
        | _, _ => .stuck
      else if isReuseOp P.base.size i then
        match decodeReset P.base.size i, decodeReuse P.base.size i with
        | some (slotReg, x, ci, mask, uniq), none =>
          match heapCtorAt P.base.ctors ci with
          | some ctor =>
            match Own.Plain.evalResetMask fr.env H x ctor mask uniq with
            | .ok (sv, H') => .next (.run { fr with rest, env := fr.env.insert slotReg sv } stk H') false
            | .resource r => .fail r
            | .trap => .trap
            | .timeout | .stuck => .stuck
          | none => .stuck
        | none, some (dst, slotReg, ci, uniq, args) =>
          match heapCtorAt P.base.ctors ci, fr.env.get? slotReg with
          | some ctor, some sv =>
            match Own.Plain.evalReuseVal fr.env H sv ctor args uniq with
            | .ok (v, H') => .next (.run { fr with rest, env := fr.env.insert dst v } stk H') false
            | .resource r => .fail r
            | .trap => .trap
            | .timeout | .stuck => .stuck
          | _, _ => .stuck
        | _, _ => .stuck
      else Cfg.step .rc P.base s
    | [] => Cfg.step .rc P.base s
  | _ => Cfg.step .rc P.base s

end IxCC.Cfg.Rc
