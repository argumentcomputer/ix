import IxCC.Xv.Operands
import IxCC.Xv.WellFormed
import IxCC.Xv.XlSemantics

/-!
# Analyses for the allocator (untrusted)

Precise liveness, loop depth, spill weights and register hints over an Xv
function (05 §5). The allocator is `produce` code (D17): it may use hash
maps and arrays, and nothing here needs to be right for soundness, since the
validator re-checks the allocation. It must be right for the allocation to
be accepted.

- **Liveness** is the backward data-flow fixpoint over blocks. A block's
  uses are its instructions' uses, its terminator's, and its edge
  arguments (read at the end of the block); block parameters are defined
  on entry.
- **Loop depth** counts the natural loops containing a block: a back edge
  `b → h` has `h` dominating `b`, and its loop is `h` plus every block that
  reaches `b` without passing through `h`.
- **Spill weight** follows regalloc2 (`liveranges.rs:36-52`): each operand
  adds `1000 · 4^depth`, plus 2000 for a definition, 2000 for a `reg` or
  `fixed` constraint and 1000 for `any`.
- **Hints**: the first fixed register each register is used in, and
  whether a register is live across a call (then callee-saved registers
  are preferred).
-/

namespace IxCC.Xv.Alloc

open IxCC.Lir (VReg Label Operand Kind Pos Con)

/-- Operands of instruction `i` of a block (`i = body.size`: the terminator). -/
def opsAt (b : Block VReg) (i : Nat) : List (Operand VReg) :=
  if h : i < b.body.size then b.body[i].operands else b.term.operands

def opUses (ops : List (Operand VReg)) : List VReg := (ops.filter (·.kind == .use)).map (·.v)

def opDefs (ops : List (Operand VReg)) : List VReg := (ops.filter (·.kind == .define)).map (·.v)

structure Info where
  /-- Blocks in reverse postorder. -/
  order : Array Label
  preds : Array (List Label)
  depth : Array Nat
  /-- Live on entry, after parameters are bound (parameters that are used
  included). -/
  liveIn : Array (Std.HashSet VReg)
  /-- Live at the end: successors' live-ins (parameters excluded) and edge
  arguments. -/
  liveOut : Array (Std.HashSet VReg)
  /-- Registers live after some call. -/
  crossCall : Std.HashSet VReg
  /-- For each register live across some call, the registers clobbered or
  overwritten by those calls. -/
  callClobbers : Std.HashMap VReg (List X86.GPR) := {}
  /-- Per-register per-block liveness intervals `(blockId, firstPos, lastPos)`. -/
  spans : Std.HashMap VReg (Array (Nat × Nat × Nat)) := {}
  weight : Std.HashMap VReg Nat
  /-- The register of a register's first fixed use. -/
  fixedHint : Std.HashMap VReg X86.GPR
  /-- Whether a block is a loop header (the target of a back edge). -/
  header : Array Bool
  deriving Inhabited

/-- Whether `u` and `v` have overlapping liveness intervals in any block. -/
def Info.interferes (info : Info) (u v : VReg) : Bool :=
  if u == v then true
  else
    let su := info.spans.getD u #[]
    let sv := info.spans.getD v #[]
    su.any fun (b, l1, r1) =>
      sv.any fun (b', l2, r2) =>
        b == b' && l1 ≤ r2 && l2 ≤ r1

/-- The live set at the top of block `b`, given the live set at its end. -/
def liveTop (b : Block VReg) (out : Std.HashSet VReg) : Std.HashSet VReg := Id.run do
  let mut live := out
  let n := b.body.size
  let tops := b.term.operands
  for x in opDefs tops do live := live.erase x
  for x in opUses tops do live := live.insert x
  for k in [:n] do
    let i := n - 1 - k
    let ops := opsAt b i
    for x in opDefs ops do live := live.erase x
    for x in opUses ops do live := live.insert x
  return live

/-- Loop depth of each block and whether it heads a loop. -/
def loopDepth (f : Func VReg) (preds : Array (List Label)) : Array Nat × Array Bool := Id.run do
  let n := f.blocks.size
  let g := f.skeleton
  let doms := g.dominators
  let mut depth := Array.replicate n 0
  let mut header := Array.replicate n false
  -- Group back edges by header, then take the union of their loops.
  for h in [:n] do
    let latches := (preds[h]!).filter fun b => Lir.Func.dominates doms h b
    if latches.isEmpty then continue
    header := header.set! h true
    let mut inLoop := (Array.replicate n false).set! h true
    let mut stack := latches
    for _ in [:n * n + n + 1] do
      match stack with
      | [] => break
      | b :: rest =>
          stack := rest
          if !inLoop[b]! then
            inLoop := inLoop.set! b true
            stack := preds[b]! ++ stack
    for b in [:n] do
      if inLoop[b]! then depth := depth.modify b (· + 1)
  return (depth, header)

def spillWeight (depth : Nat) (o : Operand VReg) : Nat :=
  let hot := 1000 * 4 ^ (min depth 10)
  let def_ := if o.kind == .define then 2000 else 0
  let con := match o.con with
    | .any => 1000
    | .reg | .fixed _ => 2000
    | _ => 0
  hot + def_ + con

def analyse (f : Func VReg) (env : Option Xl.Env := none) : Info := Id.run do
  let n := f.blocks.size
  let g := f.skeleton
  let order := g.rpo
  let preds := g.preds
  let (depth, header) := loopDepth f preds
  -- Liveness to a fixpoint, visiting blocks in postorder.
  let mut liveIn : Array (Std.HashSet VReg) := Array.replicate n {}
  let mut liveOut : Array (Std.HashSet VReg) := Array.replicate n {}
  let post := order.reverse
  let mut changed := true
  for _ in [:n + 2] do
    if !changed then break
    changed := false
    for b in post do
      let block := f.blocks[b]!
      let mut out : Std.HashSet VReg := {}
      for e in block.term.edges do
        for x in e.args do out := out.insert x
        match f.blocks[e.target]? with
        | some s =>
            for x in liveIn[e.target]! do
              if !s.params.contains x then out := out.insert x
        | none => pure ()
      let top := liveTop block out
      if top.size != liveIn[b]!.size || out.size != liveOut[b]!.size then changed := true
      liveIn := liveIn.set! b top
      liveOut := liveOut.set! b out
  -- Registers live across calls; call clobbers; block spans; weights; fixed hints.
  let mut crossCall : Std.HashSet VReg := {}
  let mut callClobbers : Std.HashMap VReg (List X86.GPR) := {}
  let mut spans : Std.HashMap VReg (Array (Nat × Nat × Nat)) := {}
  let mut weight : Std.HashMap VReg Nat := {}
  let mut fixedHint : Std.HashMap VReg X86.GPR := {}
  let touch (lo hi : Std.HashMap VReg Nat) (x : VReg) (pos : Nat) :
      Std.HashMap VReg Nat × Std.HashMap VReg Nat :=
    let lo := match lo[x]? with
      | some p => if pos < p then lo.insert x pos else lo
      | none => lo.insert x pos
    let hi := match hi[x]? with
      | some p => if pos > p then hi.insert x pos else hi
      | none => hi.insert x pos
    (lo, hi)
  for b in order do
    let block := f.blocks[b]!
    let nb := block.body.size
    let mut live := liveOut[b]!
    for x in opDefs block.term.operands do live := live.erase x
    for x in opUses block.term.operands do live := live.insert x
    for k in [:nb] do
      let i := nb - 1 - k
      let ops := opsAt block i
      for x in opDefs ops do live := live.erase x
      if let .call g .. := block.body[i]! then
        let baseClob := match env with
          | some e => e.clobbers g
          | none => X86.SysV.callerSaved.toList
        for x in live do
          crossCall := crossCall.insert x
          let mut clob := callClobbers.getD x []
          for r in baseClob do
            if !clob.contains r then clob := r :: clob
          for o in ops do
            if let .fixed r := o.con then
              if (o.kind == .define || o.v != x) && !clob.contains r then
                clob := r :: clob
          callClobbers := callClobbers.insert x clob
      for x in opUses ops do live := live.insert x
    let mut lo : Std.HashMap VReg Nat := {}
    let mut hi : Std.HashMap VReg Nat := {}
    for x in liveIn[b]! do (lo, hi) := touch lo hi x 0
    for x in block.params do (lo, hi) := touch lo hi x 0
    for i in [:nb + 1] do
      for o in opsAt block i do
        (lo, hi) := touch lo hi o.v (i + 1)
        weight := weight.insert o.v (weight.getD o.v 0 + spillWeight depth[b]! o)
        if let .fixed r := o.con then
          if o.kind == .use && !fixedHint.contains o.v then fixedHint := fixedHint.insert o.v r
    for x in block.term.edgeUses do (lo, hi) := touch lo hi x (nb + 1)
    for x in liveOut[b]! do (lo, hi) := touch lo hi x (nb + 1)
    for e in block.term.edges do
      if let some succ := f.blocks[e.target]? then
        for p in succ.params do
          (lo, hi) := touch lo hi p nb
          (lo, hi) := touch lo hi p (nb + 1)
    for (x, l) in lo.toList do
      let r := hi.getD x l
      spans := spans.insert x ((spans.getD x #[]).push (b, l, r))
  return { order, preds, depth, liveIn, liveOut, crossCall, callClobbers, spans, weight, fixedHint, header }

/-- For each register used in block `b`, the positions of its uses (edge
arguments at the terminator's position). -/
def usePositions (b : Block VReg) : Std.HashMap VReg (Array Nat) := Id.run do
  let n := b.body.size
  let mut m : Std.HashMap VReg (Array Nat) := {}
  for i in [:n + 1] do
    for x in opUses (opsAt b i) do m := m.insert x ((m.getD x #[]).push i)
  for x in b.term.edgeUses do m := m.insert x ((m.getD x #[]).push n)
  return m

end IxCC.Xv.Alloc
