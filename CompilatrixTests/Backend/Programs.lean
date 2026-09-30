import Compilatrix.Xv.XlSemantics

/-!
# Hand-written Xl programs for the backend

Allocated by hand, in the internal convention (05 §6: arguments in `rdi
rsi rdx rcx r8 r9 r10` then `outArg`/`inArg` cells, results in `rax
rdx`), so each exercises one part of stacking:

| Program | What it exercises |
| --- | --- |
| `leaf` | a frameless leaf: no frame, no stack check |
| `slots` | a small frame of slots, unchecked (frame + return address within the slack) |
| `bigFrame` | a frame too big for the slack, so the leaf checks the stack |
| `calls` | calls, a caller keeping values in a callee-saved register and a slot, a callee saving the callee-saved register it writes |
| `stackArgs` | nine arguments: two through `outArg` cells into the callee's `inArg` cells |
| `countdown` | tail calls in a framed, checked function: constant stack at any depth |
| `deep` | recursion to a given depth, then success or a failure (heap, natOverflow, trap) from the bottom of the call chain; with a small stack budget, status 2 |
| `heap` | loads and stores through the context's heap pointer |
| `fused` | a fused `cmp`/`setcc` (with its zeroing `xor`), a fused `cmp`/`cmovcc`, `div` and a shift by `cl` |
-/

namespace CompilatrixTests.Backend.Programs

open Compilatrix Compilatrix.Xv

def r (g : X86.GPR) : Loc := .reg g
def s (i : Nat) : Loc := .slot i

def row (mn : X86.Mnemonic) (w : X86.Width) (form : X86.OpEn) : X86.Op := { mn, w, form }
def addRM : X86.Op := row .add .w64 .RM
def addMR : X86.Op := row .add .w64 .MR
def addMI8 : X86.Op := row .add .w64 .MI8
def subMI8 : X86.Op := row .sub .w64 .MI8
def cmpMI8 : X86.Op := row .cmp .w64 .MI8
def cmpMR : X86.Op := row .cmp .w64 .MR
def movRM : X86.Op := row .mov .w64 .RM
def movMR : X86.Op := row .mov .w64 .MR
def movOI : X86.Op := row .mov .w32 .OI

def add (d : Loc) (a : XArg Loc) : Inst Loc := .op addMR [d] [.r d, a]
def addImm (d : Loc) (k : UInt64) : Inst Loc := .op addMI8 [d] [.r d, .i k]
def subImm (d : Loc) (k : UInt64) : Inst Loc := .op subMI8 [d] [.r d, .i k]
def movImm (d : Loc) (k : UInt64) : Inst Loc := .op movOI [d] [.i k]

def to (l : Nat) : Edge Loc := ⟨l, []⟩
/-- `if a = k then t else f`. -/
def ifEq (a : Loc) (k : UInt64) (t f : Nat) : Term Loc := .jcc cmpMI8 [.r a, .i k] [] .eq (to t) (to f)

def exported (name : String) (funcs : List (Func Loc)) : LProgram :=
  { funcs := (funcs.zipIdx.map fun (f, i) => if i == 0 then { f with conv := .sysvExport name } else f).toArray,
    main := 0 }

/-- `a + b` in a frameless leaf. -/
def leaf : LProgram := exported "t_leaf" [{ name := "leaf", params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.move (r .rax) (r .rdi), add (r .rax) (.r (r .rsi))], term := .ret [r .rax] }] }]

/-- Through three slots: `(a + b) + 5`. -/
def slots : LProgram := exported "t_slots" [{ name := "slots", params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.move (s 0) (r .rdi), .move (s 1) (r .rsi), .move (r .rax) (s 0),
      .op addRM [r .rax] [.r (r .rax), .r (s 1)], .move (s 2) (r .rax), addImm (s 2) 5, .move (r .rax) (s 2)]
    term := .ret [r .rax] }] }]

/-- Nine slots, each `a + i`, summed. -/
def bigFrame : LProgram := exported "t_big" [{ name := "big", params := [r .rdi], results := 1, blocks := #[
  { body := ((List.range 9).flatMap (fun i =>
        [Inst.move (r .rcx) (r .rdi), addImm (r .rcx) (UInt64.ofNat i), .move (s i) (r .rcx)])).toArray ++
      #[.zero (r .rax)] ++ ((List.range 9).map fun i => Inst.op addRM [r .rax] [.r (r .rax), .r (s i)]).toArray
    term := .ret [r .rax] }] }]

/-- `inc x = x + 2` (a tagged successor), clobbering `rcx`, `r11` and the
callee-saved `rbx`. -/
def inc : Func Loc := { name := "inc", params := [r .rdi], results := 1, blocks := #[
  { body := #[.move (r .rax) (r .rdi), addImm (r .rax) 2, .zero (r .rcx), .zero (r .r11), .zero (r .rbx)]
    term := .ret [r .rax] }] }

/-- `inc (inc n) + n + n`, keeping `n` in `rbx` and in a slot across the calls. -/
def calls : LProgram := exported "t_calls" [{ name := "calls", params := [r .rdi], results := 1, blocks := #[
  { body := #[.move (r .rbx) (r .rdi), .move (s 0) (r .rdi), .call 1 [r .rdi] [r .rax], .move (r .rdi) (r .rax),
      .call 1 [r .rdi] [r .rax], add (r .rax) (.r (r .rbx)), .op addRM [r .rax] [.r (r .rax), .r (s 0)]]
    term := .ret [r .rax] }] }, inc]

/-- `sum9 a₀ … a₈ = a₀ + a₆ + a₇ + a₈`, called with `a_i = n + i`. -/
def sum9 : Func Loc := { name := "sum9", params := (List.range 9).map Xl.paramLoc, results := 1, blocks := #[
  { body := #[.move (r .rax) (.inArg 0), .op addRM [r .rax] [.r (r .rax), .r (.inArg 1)],
      add (r .rax) (.r (r .rdi)), add (r .rax) (.r (r .r10))]
    term := .ret [r .rax] }] }

def stackArgs : LProgram := exported "t_stackargs" [{ name := "stackargs", params := [r .rdi], results := 1, blocks := #[
  { body := #[.move (r .rax) (r .rdi)] ++
      ((List.range 9).reverse.flatMap fun i =>
        [Inst.move (r .r11) (r .rax), addImm (r .r11) (UInt64.ofNat i), .move (Xl.argLoc i) (r .r11)]).toArray ++
      #[.call 1 ((List.range 9).map Xl.argLoc) [r .rax]]
    term := .ret [r .rax] }] }, sum9]

/-- `countdown n = if n = 0 then 42 else countdown (n - 1)` on tagged
`Nat`s, by tail calls from a frame of nine slots (checked). -/
def countdownF : Func Loc := { name := "countdown", params := [r .rdi], results := 1, blocks := #[
  { body := ((List.range 9).map fun i => Inst.move (s i) (r .rdi)).toArray, term := ifEq (r .rdi) 1 1 2 },
  { body := #[movImm (r .rax) 85], term := .ret [r .rax] },
  { body := #[.move (r .rdi) (s 8), subImm (r .rdi) 2], term := .tail 1 [r .rdi] }] }

def countdown : LProgram := exported "t_countdown" [{ name := "start", params := [r .rdi], results := 1, blocks := #[
  { term := .tail 1 [r .rdi] }] }, countdownF]

/-- `down depth mode`: recurse `depth` times (adding 1 per level on the way
back), then by `mode`: 0 returns 42, 1 fails heap, 2 natOverflow, else
traps. -/
def down : Func Loc := { name := "down", params := [r .rdi, r .rsi], results := 1, blocks := #[
  { term := ifEq (r .rdi) 1 1 2 },
  { term := ifEq (r .rsi) 1 3 4 },
  { body := #[subImm (r .rdi) 2, .move (s 0) (r .rsi), .call 1 [r .rdi, r .rsi] [r .rax], addImm (r .rax) 2]
    term := .ret [r .rax] },
  { body := #[movImm (r .rax) 85], term := .ret [r .rax] },
  { term := ifEq (r .rsi) 3 5 6 },
  { term := .fail .heap, cold := true },
  { term := ifEq (r .rsi) 5 7 8 },
  { term := .fail .natOverflow, cold := true },
  { term := .trap, cold := true }] }

def deep : LProgram := exported "t_deep" [{ name := "deep", params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.call 1 [r .rdi, r .rsi] [r .rax]], term := .ret [r .rax] }] }, down]

/-- Store `a` and `b` into the heap (`regionBase`, `ctx − 24`), load them
back and add. -/
def heap : LProgram := exported "t_heap" [{ name := "heap", params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[.op movRM [r .rcx] [.m { base := some .ctx, disp := -24 }],
      .op movMR [] [.m { base := some (.r (r .rcx)), disp := 8 }, .r (r .rdi)],
      .op movMR [] [.m { base := some (.r (r .rcx)), disp := 16 }, .r (r .rsi)],
      .op movRM [r .rax] [.m { base := some (.r (r .rcx)), disp := 8 }],
      .op addRM [r .rax] [.r (r .rax), .m { base := some (.r (r .rcx)), disp := 16 }]]
    term := .ret [r .rax] }] }]

/-- `(a < b) + max a b + a / b + a << (b & 7)` from a fused `cmp`/`setb`,
a fused `cmp`/`cmova`, `div` and `shl … cl`. Word arguments; `b ≠ 0`. -/
def fused : LProgram := exported "t_fused" [{ name := "fused", params := [r .rdi, r .rsi], results := 1, blocks := #[
  { body := #[
      .fused cmpMR [.r (r .rdi), .r (r .rsi)] (X86.Op.setccM .unsignedLt) [r .r8] [],
      .move (r .r9) (r .rsi),
      .fused cmpMR [.r (r .rdi), .r (r .rsi)] (X86.Op.cmovRM .unsignedGt .w64) [r .r9] [.r (r .r9), .r (r .rdi)],
      .move (r .rax) (r .rdi), .zero (r .rdx),
      .op (X86.Op.divM .w64) [r .rax, r .rdx] [.r (r .rsi), .r (r .rax), .r (r .rdx)],
      .move (r .rcx) (r .rsi), .op (row .and .w64 .MI8) [r .rcx] [.r (r .rcx), .i 7],
      .move (r .rdx) (r .rdi), .op (row .shl .w64 .MC) [r .rdx] [.r (r .rdx), .r (r .rcx)],
      add (r .rax) (.r (r .rdx)), add (r .rax) (.r (r .r8)), add (r .rax) (.r (r .r9))]
    term := .ret [r .rax] }] }]

end CompilatrixTests.Backend.Programs
