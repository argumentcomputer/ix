import Compilatrix.Xv.Select.Rules
import Compilatrix.Xv.Select.Cond

/-!
# Terminator rules

| Lir | Xv | Rule |
| --- | --- | --- |
| `br c w a b` | `jcc (cmp r/m, r)`, `cmp r/m, imm8` (83 /7) or `imm32`, the condition swapped if `a` is an immediate | 1 (`br.cmp*`, `br.swap`) |
| `br tz/tnz w a b` | `jcc (and r/m, r/imm)` with `je`/`jne`, the result dead | 2 (`br.and`, until `test`) |
| `br c w (load m) b` | `jcc (cmp [m], r/imm)` | 3 (`br.cmpMem`) |
| `brOvf addC x a b` / `subB` | `jcc (add/sub r/m64, r/imm)` defining `x` (tied to `a`), `jb` = `jc` on carry or borrow (06 S9) | 4 (`brOvf.add`, `brOvf.sub`) |
| `jump`, `ret`, `tail`, `fail`, `trap` | the same, immediates materialized | `jmp`, `ret`, `tail`, `exit` |

The flag producer is part of the `jcc` terminator, so no edit can separate
it from the branch (05 §3). Edge and return arguments are registers at Xv,
so immediates are materialized before the terminator. Rule 2 uses `and`
until M1.B1 adds `test` (whose result is not written); the zero test `test
a, a` (rule 1's `b = 0` case) waits for it too, and `cmp a, 0` stands in.
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Word)

/-- An edge with register arguments. -/
def edgeArgs (e : Lir.Edge) : SelM (Edge VReg × List (Inst VReg)) := do
  let (vs, pre) ← argRegs e.args
  return ({ target := e.target, args := vs }, pre)

/-- The producer operands of `op r/m, r` or `op r/m, imm` with `a` in the
r/m slot: the row and its arguments, materializing an immediate that does
not fit. -/
def producerArgs (mn : X86.Mnemonic) (w : X86.Width) (a : XArg VReg) (b : Lir.Arg) (tag : String) :
    SelM (X86.Op × List (XArg VReg) × List (Inst VReg)) := do
  match b with
  | .v b =>
      fire s!"{tag}"
      return (row mn w .MR, [a, .r b], [])
  | .imm k =>
      match imm8? w k with
      | some c =>
          fire s!"{tag}Imm8"
          return (row mn w .MI8, [a, .i c], [])
      | none =>
      match immFull? w k with
      | some c =>
          fire s!"{tag}Imm32"
          return (row mn w .MI, [a, .i c], [])
      | none =>
          let (t, pre) ← materialize k
          fire s!"{tag}"
          return (row mn w .MR, [a, .r t], pre)

/-- Rule 1 and rule 3: compare and branch. -/
def selectCmp (cx : X86.Condition) (w : X86.Width) (a b : Lir.Arg) (t f : Edge VReg) :
    SelM (List (Inst VReg) × Term VReg) := do
  let site := (← read).block.body.size
  let jcc (p : X86.Op) (args : List (XArg VReg)) (c : X86.Condition) : Term VReg := .jcc p args [] c t f
  -- Rule 3: fold a single-use load into the compare.
  if let .v a' := a then
    if let some m ← sinkLoad? a' site w.bytes then
      let (p, args, pre) ← producerArgs .cmp w (.m m) b "br.cmpMem"
      return (pre, jcc p args cx)
  if let .v b' := b then
    if let some m ← sinkLoad? b' site w.bytes then
      let (p, args, pre) ← producerArgs .cmp w (.m m) a "br.cmpMem"
      return (pre, jcc p args (swapCond cx))
  match a, b with
  | .v a, b =>
      let (p, args, pre) ← producerArgs .cmp w (.r a) b "br.cmp"
      return (pre, jcc p args cx)
  | .imm k, .v b =>
      fire "br.swap"
      let (p, args, pre) ← producerArgs .cmp w (.r b) (.imm k) "br.cmp"
      return (pre, jcc p args (swapCond cx))
  | .imm ka, .imm kb =>
      let (x, pre₁) ← materialize ka
      let (p, args, pre₂) ← producerArgs .cmp w (.r x) (.imm kb) "br.cmp"
      return (pre₁ ++ pre₂, jcc p args cx)

/-- Rule 2: `a &&& b` is zero (`tz`) or not, by a flag-setting `and` whose
result is dead. -/
def selectAndTest (zero : Bool) (w : X86.Width) (a b : Lir.Arg) (t f : Edge VReg) :
    SelM (List (Inst VReg) × Term VReg) := do
  let d ← fresh
  let cc : X86.Condition := if zero then .eq else .ne
  let (a, b, pre₁) ← match a, b with
    | .v a, b => pure (a, b, [])
    | .imm k, .v b => pure (b, Lir.Arg.imm k, [])
    | .imm ka, .imm kb => do
        let (x, pre) ← materialize ka
        pure (x, Lir.Arg.imm kb, pre)
  let (p, args, pre₂) ← producerArgs .and w (.r a) b "br.and"
  return (pre₁ ++ pre₂, .jcc p args [d] cc t f)

/-- Rule 4: `x := a ± b`, then the carry or borrow edge. -/
def selectBrOvf (o : Lir.Ovf) (x : VReg) (a b : Lir.Arg) (ok ovf : Edge VReg) :
    SelM (List (Inst VReg) × Term VReg) := do
  let (mn, tag) := match o with
    | .addC => (X86.Mnemonic.add, "brOvf.add")
    | .subB => (.sub, "brOvf.sub")
  let (a, b, pre₁) ← match o, a, b with
    | _, .v a, b => pure (a, b, [])
    | .addC, .imm k, .v b => pure (b, Lir.Arg.imm k, [])
    | _, .imm k, b => do
        let (t, pre) ← materialize k
        pure (t, b, pre)
  let (p, args, pre₂) ← producerArgs mn .w64 (.r a) b tag
  -- The branch is taken on carry (borrow): the overflow edge.
  return (pre₁ ++ pre₂, .jcc p args [x] .unsignedLt ovf ok)

/-- The Xv terminator for a Lir terminator, and the instructions that must
precede it. -/
def selectTerm : Lir.Term → SelM (List (Inst VReg) × Term VReg)
  | .jump e => do
      let (e, pre) ← edgeArgs e
      fire "jmp"
      return (pre, .jmp e)
  | .br c w a b t f => do
      let (t, pt) ← edgeArgs t
      let (f, pf) ← edgeArgs f
      let (pre, term) ← match condX86 c with
        | some cx => selectCmp cx w a b t f
        | none => selectAndTest (c == .tz) w a b t f
      return (pt ++ pf ++ pre, term)
  | .brOvf o x a b ok ovf => do
      let (ok, p₁) ← edgeArgs ok
      let (ovf, p₂) ← edgeArgs ovf
      let (pre, term) ← selectBrOvf o x a b ok ovf
      return (p₁ ++ p₂ ++ pre, term)
  | .ret as => do
      let (vs, pre) ← argRegs as
      fire "ret"
      return (pre, .ret vs)
  | .tail g as => do
      let (vs, pre) ← argRegs as
      fire "tail"
      return (pre, .tail g vs)
  | .fail r => do
      fire "exit"
      return ([], .fail r)
  | .trap => do
      fire "exit"
      return ([], .trap)

end Compilatrix.Xv.Select
