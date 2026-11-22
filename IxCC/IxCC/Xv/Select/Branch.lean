import IxCC.Xv.Select.Rules

/-!
# Terminator rules

| Lir | Xv | Rule |
| --- | --- | --- |
| `br c w a b` | `jcc` with the flag producer of `Select.Producer` (`cmp`, `test a, a`, `test`, a folded load) | 1–3 |
| `brOvf addC x a b` / `subB` | `jcc (add/sub r/m64, r/imm)` defining `x` (tied to `a`), `jb` = `jc`
on carry or borrow | 4 (`brOvf.add*`, `brOvf.sub*`) |
| `brOvf … (load m)` | `jcc (add/sub r64, m64)` (RM) | 4, 9 (`brOvf.addMem`, `brOvf.subMem`) |
| `jump`, `ret`, `tail`, `fail`, `trap` | the same, immediates materialized | `jmp`, `ret`, `tail`, `exit` |

The flag producer is part of the `jcc` terminator, so no edit can separate
it from the branch. Edge and return arguments are registers at Xv,
so immediates are materialized before the terminator. -/

namespace IxCC.Xv.Select

open IxCC.Lir (VReg Word)

/-- An edge with register arguments. -/
def edgeArgs (e : Lir.Edge) : SelM (Edge VReg × List (Inst VReg)) := do
  let (vs, pre) ← argRegs e.args
  return ({ target := e.target, args := vs }, pre)

/-- Rule 4: `x := a ± b`, then the carry or borrow edge; a single-use
64-bit load folds into `add/sub r, m` (the second operand, or either for
`addC`). -/
def selectBrOvf (o : Lir.Ovf) (x : VReg) (a b : Lir.Arg) (ok ovf : Edge VReg) :
    SelM (List (Inst VReg) × Term VReg) := do
  let site ← sitePos
  let (mn, tag) := match o with
    | .addC => (X86.Mnemonic.add, "brOvf.add")
    | .subB => (.sub, "brOvf.sub")
  -- The branch is taken on carry (borrow): the overflow edge.
  let jcc (p : X86.Op) (args : List (XArg VReg)) : Term VReg := .jcc p args [x] .unsignedLt ovf ok
  if let (.v a', .v b') := (a, b) then
    if let some m ← sinkLoad? b' site 8 then
      fire s!"{tag}.mem"
      return ([], jcc (row mn .w64 .RM) [.r a', .m m])
    if o == .addC then
      if let some m ← sinkLoad? a' site 8 then
        fire s!"{tag}.mem"
        return ([], jcc (row mn .w64 .RM) [.r b', .m m])
  let (a, b, pre₁) ← match o, a, b with
    | _, .v a, b => pure (a, b, [])
    | .addC, .imm k, .v b => pure (b, Lir.Arg.imm k, [])
    | _, .imm k, b => do
        let (t, pre) ← materialize k
        pure (t, b, pre)
  let (p, args, pre₂) ← producerArgs mn .w64 (.r a) b tag
  return (pre₁ ++ pre₂, jcc p args)

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
      let pr ← compareProducer c w a b
      fire "br"
      return (pt ++ pf ++ pr.pre, .jcc pr.op pr.args [] pr.cond t f)
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

end IxCC.Xv.Select
