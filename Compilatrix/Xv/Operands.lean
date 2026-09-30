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

/-! ## Substituting operands

`Inst.substitute ls i` gives `i` the operands `ls`, one per entry of
`i.operands` and in that order: the uses in argument order, then the
definitions. This is the substitution of the allocator's `apply` (05 §5),
which never rewrites an instruction otherwise. `check-xv-select` checks
that substituting an instruction's own operands gives it back. -/

variable {σ : Type}

def takeOne : List σ → Option (σ × List σ)
  | x :: xs => some (x, xs)
  | [] => none

def Amode.substitute (a : Amode ρ) (ls : List σ) : Option (Amode σ × List σ) := do
  let (base, ls) ← match a.base with
    | none => pure (none, ls)
    | some .ctx => pure (some .ctx, ls)
    | some (.r _) => do
        let (x, ls) ← takeOne ls
        pure (some (.r x), ls)
  let (index, ls) ← match a.index with
    | none => pure (none, ls)
    | some (_, s) => do
        let (x, ls) ← takeOne ls
        pure (some (x, s), ls)
  pure ({ base, index, disp := a.disp }, ls)

def XArg.substitute (a : XArg ρ) (ls : List σ) : Option (XArg σ × List σ) :=
  match a with
  | .r _ => do
      let (x, ls) ← takeOne ls
      pure (.r x, ls)
  | .m am => do
      let (am, ls) ← am.substitute ls
      pure (.m am, ls)
  | .i w => pure (.i w, ls)

def substituteArgs : List (XArg ρ) → List σ → Option (List (XArg σ) × List σ)
  | [], ls => some ([], ls)
  | a :: as, ls => do
      let (a, ls) ← a.substitute ls
      let (as, ls) ← substituteArgs as ls
      pure (a :: as, ls)

def Inst.substitute (ls : List σ) : Inst ρ → Option (Inst σ)
  | .op o defs args => do
      let (args, rest) ← substituteArgs args ls
      guard (rest.length == defs.length)
      pure (.op o rest args)
  | .fused p pargs c defs cargs => do
      let (pargs, rest) ← substituteArgs pargs ls
      let (cargs, rest) ← substituteArgs cargs rest
      guard (rest.length == defs.length)
      pure (.fused p pargs c rest cargs)
  | .move .. =>
      match ls with
      | [src, dst] => some (.move dst src)
      | _ => none
  | .zero _ =>
      match ls with
      | [x] => some (.zero x)
      | _ => none
  | .call f args rets =>
      if ls.length == args.length + rets.length then
        some (.call f (ls.take args.length) (ls.drop args.length))
      else none

/-- A terminator with operands `ls` (as `Term.operands` orders them) and
edge arguments `edgeArgs`, one list per edge. -/
def Term.substitute (ls : List σ) (edgeArgs : List (List σ)) (t : Term ρ) : Option (Term σ) := do
  let edges ← if t.edges.length == edgeArgs.length then
      pure ((t.edges.zip edgeArgs).map fun (e, args) => ({ target := e.target, args } : Edge σ))
    else none
  match t, edges with
  | .jmp _, [e] => guard ls.isEmpty; pure (.jmp e)
  | .jcc p pargs defs c _ _, [e₁, e₂] => do
      let (pargs, rest) ← substituteArgs pargs ls
      guard (rest.length == defs.length)
      pure (.jcc p pargs rest c e₁ e₂)
  | .ret vs, [] => do guard (ls.length == vs.length); pure (.ret ls)
  | .tail f args, [] => do guard (ls.length == args.length); pure (.tail f ls)
  | .fail r, [] => do guard ls.isEmpty; pure (.fail r)
  | .trap, [] => do guard ls.isEmpty; pure .trap
  | _, _ => none

end Compilatrix.Xv
