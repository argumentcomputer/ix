import Compilatrix.Cfg.Rc.Syntax
import Compilatrix.Cfg.Semantics
import Compilatrix.Own.Plain.Semantics

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc
open Compilatrix.Own (RVal Heap)

def actionStep (fr : Frame) (stk : List (Frame × Fir.Var)) (H : Heap) (rest : List Instr) (a : Action) :
    Sem.Step State (RVal × Heap) :=
  match Own.Plain.evalAction fr.env H a with
  | .ok H' => .next (.run { fr with rest } stk H') false
  | .resource r => .fail r
  | .trap => .trap
  | .timeout | .stuck => .stuck

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
      else Cfg.step .rc P.base s
    | [] => Cfg.step .rc P.base s
  | _ => Cfg.step .rc P.base s

end Compilatrix.Cfg.Rc
