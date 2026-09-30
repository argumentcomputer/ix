import Compilatrix.Xv.Select.Driver
import Compilatrix.Xv.WellFormed
import Compilatrix.Xv.Semantics
import Compilatrix.Xv.Print
import CompilatrixTests.Lir.Region

/-!
# Shared helpers for the Xv tests

Selecting a Lir program, comparing `Lir.eval` with `Xv.eval` on outcome,
values and final heap and context words, and stepping Xv by hand to count
the clock charges it spends.
-/

namespace CompilatrixTests.Xv

open Compilatrix Compilatrix.Lir Compilatrix.Xv CompilatrixTests.Lir

/-- A comparable summary of an outcome: values, then heap and context words
(`Region`), or the failure. -/
inductive Digest where
  | ok (vals heap ctx : List Word)
  | timeout
  | resource (r : Sem.Resource)
  | trap
  | stuck
  deriving BEq, Repr, Inhabited

def digest : Outcome → Digest
  | .ok (vals, mem) => .ok vals (Region.heapWords mem) (Region.ctxWords mem)
  | .timeout => .timeout
  | .resource r => .resource r
  | .trap => .trap
  | .stuck => .stuck

/-- Without the final memory, which is costly to read back. -/
def light : Outcome → Digest
  | .ok (vals, _) => .ok vals [] []
  | o => digest o

def Digest.light : Digest → Digest
  | .ok vals _ _ => .ok vals [] []
  | d => d

def labels : Array String := #["ok", "timeout", "heap", "stack", "natOverflow", "trap", "stuck"]

def Digest.index : Digest → Nat
  | .ok .. => 0
  | .timeout => 1
  | .resource .heap => 2
  | .resource .stack => 3
  | .resource .natOverflow => 4
  | .trap => 5
  | .stuck => 6

def Digest.text : Digest → String
  | .ok vals _ _ => s!"ok {vals.map (·.toNat)}"
  | d => labels[d.index]!

/-- Step Xv by hand: the outcome, steps taken and charges spent. -/
def countRun (p : VProgram) (fuel k : Nat) (s : Lir.State) : Outcome × Nat × Nat := Id.run do
  let mut s := s
  let mut k := k
  let mut steps := 0
  let mut charges := 0
  for _ in [:fuel] do
    steps := steps + 1
    match Xv.step p s with
    | .next s' charge =>
        if charge then
          if k == 0 then return (.timeout, steps, charges)
          k := k - 1
          charges := charges + 1
        s := s'
    | .done v => return (.ok v, steps, charges)
    | .fail r => return (.resource r, steps, charges)
    | .trap => return (.trap, steps, charges)
    | .stuck => return (.stuck, steps, charges)
  return (.timeout, steps, charges)

/-- The selected program, or the selection error's text. -/
def select (p : Lir.Program) : Except String (VProgram × Std.HashMap String Nat) :=
  match Select.run p with
  | .ok r => .ok r
  | .error e => .error e.text

/-- The registers an instruction list reads and writes, by its operand
metadata, agree with its syntax. -/
def operandsAgree (q : VProgram) : Bool :=
  q.funcs.all fun f => f.blocks.all fun b =>
    b.body.all (fun i =>
      Lir.operandUses i.operands == i.uses && Lir.operandDefs i.operands == i.defs) &&
    (Lir.operandUses b.term.operands == b.term.uses && Lir.operandDefs b.term.operands == b.term.defs)

/-- Select, check, and compare `Lir.eval` with `Xv.eval` at clock `k` on
outcome, values and memory. -/
def agrees (p : Lir.Program) (args : List Word) (k : Nat := 1000) (seed : UInt64 := 0) : Bool :=
  match select p with
  | .error _ => false
  | .ok (q, _) =>
      q.wellFormed && operandsAgree q &&
        let mem := Region.initial seed
        digest (Lir.eval p k args mem Region.ctx) == digest (Xv.eval q k args mem Region.ctx)

/-- The instructions selected for block `b` of function 0. -/
def selected (p : Lir.Program) (b : Label := 0) : List (Inst VReg) :=
  match select p with
  | .ok (q, _) => ((q.funcs[0]?.bind (·.blocks[b]?)).map (·.body.toList)).getD []
  | .error _ => []

/-- The terminator selected for block `b` of function 0. -/
def selectedTerm (p : Lir.Program) (b : Label := 0) : Option (Term VReg) :=
  match select p with
  | .ok (q, _) => (q.funcs[0]?.bind (·.blocks[b]?)).map (·.term)
  | .error _ => none

/-- Whether rule `name` fired on `p`. -/
def fired (p : Lir.Program) (name : String) : Bool :=
  match select p with
  | .ok (_, f) => f.getD name 0 > 0
  | .error _ => false

/-- The unsupported form selection reports, if any. -/
def unsupportedForm (p : Lir.Program) : Option String :=
  match Select.run p with
  | .error e => some e.form
  | .ok _ => none

end CompilatrixTests.Xv
