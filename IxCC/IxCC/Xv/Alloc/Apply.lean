import IxCC.Xv.Alloc.Output
import IxCC.Xv.Operands
import IxCC.Xv.XlSemantics

/-!
# Applying an allocation

`Alloc.apply f o` (05 §5) is the Xl function an allocation denotes:
instructions are never rewritten, only given the locations `o` lists
(`Inst.substitute`, in `Inst.operands` order), and the edits become `move`
instructions at their positions. Edges carry no arguments at Xl (their
bindings are edits), blocks no parameters, and the function's parameters sit
where the convention puts them (`Xl.paramLoc`).

This is on `Recheck.run`'s path (the validator checks `o` and the emitted
code is `apply f o`, closing regalloc2 gap 7), so it recurses structurally
over lists. Edits must be in position order and none may follow the
terminator; `apply` fails otherwise, and the validator rejects the same
allocations.
-/

namespace IxCC.Xv.Alloc

open IxCC.Lir (VReg)

def Edit.toInst : Edit → Inst Loc
  | .move dst src => .move dst src

/-- Edits at position `i` from the front of an ordered list, and the rest. -/
def takeAt (i : Nat) : List (Nat × Edit) → List Edit × List (Nat × Edit)
  | [] => ([], [])
  | (j, e) :: rest =>
      if j == i then
        let (now, later) := takeAt i rest
        (e :: now, later)
      else ([], (j, e) :: rest)

/-- Positions nondecreasing from `prev` and at most `n` (the terminator). -/
def editsOrdered (n : Nat) : List (Nat × Edit) → Nat → Bool
  | [], _ => true
  | (i, _) :: rest, prev => decide (prev ≤ i) && decide (i ≤ n) && editsOrdered n rest i

/-- The body with edits interleaved; returns the edits left for the
terminator's position. -/
def interleave : List (Inst VReg) → List (List Loc) → List (Nat × Edit) → Nat →
    Option (List (Inst Loc) × List (Nat × Edit))
  | [], [], es, _ => some ([], es)
  | inst :: insts, ls :: lss, es, i => do
      let (now, later) := takeAt i es
      let x ← inst.substitute ls
      let (rest, left) ← interleave insts lss later (i + 1)
      pure (now.map Edit.toInst ++ x :: rest, left)
  | _, _, _, _ => none

def applyBlock (b : Block VReg) (o : BlockOut) : Except String (Block Loc) := do
  let body := b.body.toList
  unless editsOrdered body.length o.edits 0 do throw "edits are out of order or follow the terminator"
  let some (insts, left) := interleave body o.locs o.edits 0
    | throw "instruction locations do not match the operands"
  let (atTerm, rest) := takeAt body.length left
  unless rest.isEmpty do throw "edits follow the terminator"
  let some term := b.term.substitute o.termLocs (b.term.edges.map fun _ => [])
    | throw "terminator locations do not match the operands"
  pure { params := [], body := ⟨insts ++ atTerm.map Edit.toInst⟩, term, cold := b.cold }

def applyBlocks : List (Block VReg) → List BlockOut → Nat → Except String (List (Block Loc))
  | [], [], _ => pure []
  | b :: bs, o :: os, l => do
      let x ← match applyBlock b o with
        | .ok x => pure x
        | .error e => throw s!"block {l}: {e}"
      let xs ← applyBlocks bs os (l + 1)
      pure (x :: xs)
  | _, _, _ => throw "the allocation's block count differs from the function's"

/-- The Xl function allocation `o` denotes. -/
def apply (f : Func VReg) (o : Output) : Except String (Func Loc) := do
  let blocks ← applyBlocks f.blocks.toList o.blocks 0
  pure { name := f.name, params := (List.range f.params.length).map Xl.paramLoc, results := f.results
         blocks := ⟨blocks⟩, conv := f.conv }

/-- Allocate every function: `outs` holds one allocation per function. -/
def applyProgram (p : VProgram) (outs : List Output) : Except String LProgram := do
  let rec go : List (Func VReg) → List Output → Nat → Except String (List (Func Loc))
    | [], [], _ => pure []
    | f :: fs, o :: os, i => do
        let g ← match apply f o with
          | .ok g => pure g
          | .error e => throw s!"function {i}: {e}"
        pure (g :: (← go fs os (i + 1)))
    | _, _, _ => throw "the allocation's function count differs from the program's"
  let funcs ← go p.funcs.toList outs 0
  pure { funcs := ⟨funcs⟩, main := p.main }

end IxCC.Xv.Alloc
