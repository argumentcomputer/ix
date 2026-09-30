import Compilatrix.Xv.XlSemantics
import Compilatrix.Xv.Operands
import Compilatrix.Xv.Select.Basic
import CompilatrixTests.Lir.Region

/-!
# Hand-written Xl cases

Cheap assertions on `Xl.eval`, checked while this module elaborates: rows
over registers and stack cells, the width rule for stack-cell definitions,
ties and reserved registers, the call convention (arguments, results,
stack arguments, the caller's registers after a return, a runtime
procedure's smaller clobber set), tail calls, and an allocated loop that
runs in lock-step with its Xv original, clock charges included.
-/

namespace CompilatrixTests.Xv.XlCases

open Compilatrix Compilatrix.Lir Compilatrix.Xv CompilatrixTests.Lir

private def r (g : X86.GPR) : Loc := .reg g
private def s (i : Nat) : Loc := .slot i

def addMR : X86.Op := Select.row .add .w64 .MR
def addMI8 : X86.Op := Select.row .add .w64 .MI8
def cmpMR : X86.Op := Select.row .cmp .w64 .MR

def prog (funcs : Array (Func Loc)) : LProgram := { funcs, main := 0 }

def run (p : LProgram) (args : List Word) (env : Xl.Env := {}) (k := 100) : Outcome :=
  Xl.eval p env k args (Region.initial 0) Region.ctx

def values : Outcome → Option (List Word)
  | .ok (vals, _) => some vals
  | _ => none

def isStuck : Outcome → Bool
  | .stuck => true
  | _ => false

/-! ## Rows over locations -/

/-- `rax := rdi + rsi`. -/
def leaf : LProgram := prog #[{ params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.move (r .rax) (r .rdi), .op addMR [r .rax] [.r (r .rax), .r (r .rsi)]], term := .ret [r .rax] }] }]

#guard values (run leaf [3, 4]) == some [7]

/-- A slot as the r/m operand of a 64-bit read-write slot, then reloaded. -/
def spilled : LProgram := prog #[{ params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.move (s 0) (r .rdi), .op addMR [s 0] [.r (s 0), .r (r .rsi)],
      .op addMI8 [s 0] [.r (s 0), .i 0xffffffffffffffff], .move (r .rax) (s 0)]
    term := .ret [r .rax] }] }]

#guard values (run spilled [3, 4]) == some [6]

/-- A 32-bit definition in a slot is not the machine's 4-byte store: stuck. -/
def narrowSlot : LProgram := prog #[{ params := [], results := 1, blocks := #[
  { body := #[.op (Select.row .mov .w32 .MI) [s 0] [.i 5], .move (r .rax) (s 0)], term := .ret [r .rax] }] }]

#guard isStuck (run narrowSlot [])

/-- A tie whose definition is not at its use's location, `rsp` as an
operand, a stack cell in a register-only slot, and an undefined register. -/
def bad (body : Array (Inst Loc)) : LProgram := prog #[{ params := [r .rdi], results := 1, blocks := #[
  { body, term := .ret [r .rax] }] }]

#guard isStuck (run (bad #[.op addMR [r .rax] [.r (r .rdi), .r (r .rdi)]]) [1])
#guard isStuck (run (bad #[.move (r .rax) (r .rdi), .op addMR [r .rax] [.r (r .rax), .r (r .rsp)]]) [1])
#guard isStuck (run (bad #[.move (r .rax) (r .rdi), .move (s 0) (r .rdi),
    .op addMR [r .rax] [.r (r .rax), .r (s 0)]]) [1])
#guard isStuck (run (bad #[.move (r .rax) (r .rsi)]) [1])
#guard values (run (bad #[.zero (r .rax)]) [1]) == some [0]

/-! ## Calls -/

/-- `f1(x) = x + 1`, clobbering `rbx` (callee-saved) and `rcx`. -/
def inc : Func Loc := { params := [r .rdi], results := 1, blocks := #[
  { body := #[.move (r .rax) (r .rdi), .op addMI8 [r .rax] [.r (r .rax), .i 1],
      .zero (r .rbx), .zero (r .rcx)]
    term := .ret [r .rax] }] }

/-- `main(a)`: `rbx := a`, `rcx := a`, call `f1(a)`, then read `rbx` (or
`rcx`) and add it to the result. -/
def caller (after : X86.GPR) : Func Loc := { params := [r .rdi], results := 1, blocks := #[
  { body := #[.move (r .rbx) (r .rdi), .move (r .rcx) (r .rdi), .call 1 [r .rdi] [r .rax],
      .op addMR [r .rax] [.r (r .rax), .r (r after)]]
    term := .ret [r .rax] }] }

/- The callee-saved `rbx` keeps the caller's value; `rcx` is clobbered. -/
#guard values (run (prog #[caller .rbx, inc]) [5]) == some [11]
#guard isStuck (run (prog #[caller .rcx, inc]) [5])
/- A runtime procedure declaring a smaller clobber set keeps `rcx`. -/
#guard values (run (prog #[caller .rcx, inc]) [5] { clobbers := fun f => if f == 1 then [.rax] else
    X86.SysV.callerSaved.toList }) == some [11]
/-- Arguments and results must sit in the convention's locations. -/
def misplaced : LProgram := prog #[{ params := [r .rdi], results := 1, blocks := #[
  { body := #[.call 1 [r .rsi] [r .rax]], term := .ret [r .rax] }] }, inc]
#guard isStuck (run misplaced [5])

/-- Eight arguments: the eighth goes through `outArg 0` / `inArg 0`. -/
def eighth : Func Loc := { params := (List.range 8).map Xl.paramLoc, results := 1, blocks := #[
  { body := #[.move (r .rax) (.inArg 0)], term := .ret [r .rax] }] }

def callEight : Func Loc := { params := [], results := 1, blocks := #[
  { body := ((List.range 7).map fun j => Inst.op (Select.row .mov .w32 .OI) [Xl.argLoc j] [.i (UInt64.ofNat j)]).toArray ++
      #[.op (Select.row .mov .w32 .OI) [r .rax] [.i 42], .move (.outArg 0) (r .rax),
        .call 1 ((List.range 8).map Xl.argLoc) [r .rax]]
    term := .ret [r .rax] }] }

#guard values (run (prog #[callEight, eighth]) []) == some [42]

/-- A tail call replaces the frame; the result returns to `main`'s caller. -/
def tailer : Func Loc := { params := [r .rdi], results := 1, blocks := #[
  { body := #[.op addMI8 [r .rdi] [.r (r .rdi), .i 10]], term := .tail 1 [r .rdi] }] }

#guard values (run (prog #[tailer, inc]) [5]) == some [16]

/-! ## Implicit operands and fused pairs -/

/-- `rdi / rsi` and `rdi % rsi` by `div`: the dividend in `rax`, the high
half zeroed in `rdx`. -/
def divide (lo : Loc) (ret : X86.GPR) : LProgram := prog #[{ params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.move (r .rax) (r .rdi), .zero (r .rdx),
      .op (X86.Op.divM .w64) [r .rax, r .rdx] [.r (r .rsi), .r lo, .r (r .rdx)], .move (r .rax) (r ret)]
    term := .ret [r .rax] }] }]

#guard values (run (divide (r .rax) .rax) [47, 5]) == some [9]
#guard values (run (divide (r .rax) .rdx) [47, 5]) == some [2]
/- The dividend must be in `rax`; a zero divisor faults (stuck). -/
#guard isStuck (run (divide (r .rdi) .rax) [47, 5])
#guard isStuck (run (divide (r .rax) .rax) [47, 0])

/-- `rax := rdi < rsi` by a fused `cmp`/`setb` into `dst` after writing
garbage there: the expansion zeroes `dst` first, so it must not alias a use. -/
def lessThan (dst : X86.GPR) : LProgram := prog #[{ params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.op (Select.row .mov .w64 .OI) [r dst] [.i 0xdeadbeefcafe0000],
      .fused cmpMR [.r (r .rdi), .r (r .rsi)] (X86.Op.setccM .unsignedLt) [r dst] [], .move (r .rax) (r dst)]
    term := .ret [r .rax] }] }]

#guard values (run (lessThan .rcx) [3, 4]) == some [1]
#guard values (run (lessThan .rcx) [4, 3]) == some [0]
#guard isStuck (run (lessThan .rsi) [3, 4])

/-- A shift by `cl`: the count must be in `rcx`. -/
def shiftBy (count : Loc) : LProgram := prog #[{ params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.move (r .rcx) (r .rsi), .move (r .rax) (r .rdi),
      .op (Select.row .shl .w64 .MC) [r .rax] [.r (r .rax), .r count]]
    term := .ret [r .rax] }] }]

#guard values (run (shiftBy (r .rcx)) [3, 65]) == some [6]
#guard isStuck (run (shiftBy (r .rsi)) [3, 65])

/-! ## Lock-step with Xv -/

/-- `Σ i < n, i` at Xv, and a register allocation of it at Xl. -/
def sumXv : VProgram := { main := 0, funcs := #[{ params := [0], results := 1, blocks := #[
  { body := #[.zero 1, .zero 2], term := .jmp ⟨1, [1, 2]⟩ },
  { params := [3, 4], term := .jcc cmpMR [.r 3, .r 0] [] .unsignedLt ⟨2, []⟩ ⟨3, []⟩ },
  { body := #[.op addMR [5] [.r 4, .r 3], .op addMI8 [6] [.r 3, .i 1]], term := .jmp ⟨1, [6, 5]⟩ },
  { term := .ret [4] }] }] }

def sumXl : LProgram := prog #[{ params := [r .rdi], results := 1, blocks := #[
  { body := #[.zero (r .rcx), .zero (r .rax)], term := .jmp ⟨1, []⟩ },
  { term := .jcc cmpMR [.r (r .rcx), .r (r .rdi)] [] .unsignedLt ⟨2, []⟩ ⟨3, []⟩ },
  { body := #[.op addMR [r .rax] [.r (r .rax), .r (r .rcx)], .op addMI8 [r .rcx] [.r (r .rcx), .i 1]],
    term := .jmp ⟨1, []⟩ },
  { term := .ret [r .rax] }] }]

def sameAt (n k : Nat) : Bool :=
  match Xv.eval sumXv k [UInt64.ofNat n] (Region.initial 0) Region.ctx, run sumXl [UInt64.ofNat n] (k := k) with
  | .ok (a, _), .ok (b, _) => a == b
  | .timeout, .timeout => true
  | _, _ => false

#guard values (run sumXl [10] (k := 10)) == some [45]
/- The allocation as a substitution in `operands` order (uses, then definitions). -/
#guard (sumXv.funcs[0]!.blocks[2]!.body[0]!).substitute [r .rax, r .rcx, r .rax] ==
  some (sumXl.funcs[0]!.blocks[2]!.body[0]!)
#guard (sumXv.funcs[0]!.blocks[1]!.term).substitute [r .rcx, r .rdi] [[], []] ==
  some (sumXl.funcs[0]!.blocks[1]!.term)
#guard (List.range 12).all fun k => sameAt 10 k
#guard isStuck (run sumXl [10] (k := 9)) == false

end CompilatrixTests.Xv.XlCases
