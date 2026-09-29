import Compilatrix.Xv.Slots
import Compilatrix.Lir.Operands

/-!
# Xv operand metadata

The allocator's view of each instruction (05 §3, §5), derived from the
table row's slots through the same binding the executor uses
(`bindRow`), so the metadata cannot disagree with the semantics about
which operands are read and written.

- Every use is early and every definition late: a row reads all its inputs
  before it writes (`Op.exec`), and a definition may share a location with a
  use of the same instruction.
- A register argument in an r/m slot (`kinds` includes memory) is `any`: at
  Xl it may be a stack cell, read at the slot's width. A register-only slot
  and every address register are `reg`.
- A definition in an r/m slot of width 64 is `any`: an 8-byte store and a
  64-bit register write agree. A narrower definition is `reg`, since a
  32-bit register write zero-extends and a 4-byte store does not.
- A tied definition (a read-write slot) is `reuse i`, where `i` is its use's
  position in the operand list; the use is `any` or `reg` as for a
  definition of that slot, since it will be written in place.
- `call`, `ret` and `tail` operands are fixed by the internal convention
  (`Lir.Conv.argCon`, `resultCon`, 05 §6); `move` is `any` to `any`; `zero`
  defines a register.
- M1.B1's implicit register operands (`div`'s `rax`/`rdx`, a shift's `cl`)
  will be `fixed`.

Uses come first, in slot order, then definitions. Edge arguments are
block-parameter bindings, not operands (as at Lir).
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (Operand Kind Pos Con)

variable {ρ : Type}

def useAt (con : Con) (x : ρ) : Operand ρ := ⟨x, .use, .early, con⟩

def defAt (con : Con) (x : ρ) : Operand ρ := ⟨x, .define, .late, con⟩

/-- The constraint of a register read in slot `s`. -/
def readCon (s : X86.Slot) : Con := if s.kinds.contains .mem then .any else .reg

/-- The constraint of a register written in slot `s`. -/
def writeCon (s : X86.Slot) : Con :=
  if s.kinds.contains .mem && s.width == .w64 then .any else .reg

def boundUses : List (Bound ρ) → List (Operand ρ)
  | [] => []
  | b :: bs =>
      (match b with
        | .input s (.r a) => [useAt (readCon s) a]
        | .input _ (.m m) | .memory _ m => m.regs.map (useAt .reg)
        | .input _ (.i _) | .output .. => []
        | .tied s a _ => [useAt (writeCon s) a]) ++ boundUses bs

/-- Definitions of bound slots; `i` is the position of the first slot's
first use, for `reuse`. -/
def boundDefs : Nat → List (Bound ρ) → List (Operand ρ)
  | _, [] => []
  | i, b :: bs =>
      (match b with
        | .output s x => [defAt (writeCon s) x]
        | .tied _ _ x => [defAt (.reuse i) x]
        | _ => []) ++ boundDefs (i + (boundUses [b]).length) bs

def boundOperands (bs : List (Bound ρ)) : List (Operand ρ) := boundUses bs ++ boundDefs 0 bs

/-- Positional operands fixed by the convention. -/
def conUses (con : Nat → Con) (xs : List ρ) : List (Operand ρ) :=
  xs.zipIdx.map fun (x, i) => useAt (con i) x

def conDefs (con : Nat → Con) (xs : List ρ) : List (Operand ρ) :=
  xs.zipIdx.map fun (x, i) => defAt (con i) x

/-- Operands of an instruction; `[]` if its row does not bind (which
`WellFormed` rejects). -/
def Inst.operands : Inst ρ → List (Operand ρ)
  | .op o defs args => ((bindRow o defs args).map boundOperands).getD []
  | .fused p pargs c defs cargs =>
      match bindRow p [] pargs, bindRow c defs cargs with
      | some pb, some cb => boundOperands (pb ++ cb)
      | _, _ => []
  | .move dst src => [useAt .any src, defAt .any dst]
  | .zero x => [defAt .reg x]
  | .call _ args rets => conUses Lir.Conv.argCon args ++ conDefs Lir.Conv.resultCon rets

/-- Operands of a terminator; edge arguments excluded. -/
def Term.operands : Term ρ → List (Operand ρ)
  | .jcc p pargs defs _ _ _ => ((bindRow p defs pargs).map boundOperands).getD []
  | .ret vs => conUses Lir.Conv.resultCon vs
  | .tail _ args => conUses Lir.Conv.argCon args
  | .jmp _ | .fail _ | .trap => []

end Compilatrix.Xv
