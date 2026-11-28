import IxCC.Lir.Opt.Licm
import IxCC.Lir.WellFormed

/-!
# Directly-verified bounded function & self-recursive inlining (`Lir.Opt.Inline`)

Implements single-site call inlining (`inlineCallSite`) for both non-recursive
helper calls (e.g. `collatz`, `prime-count`) and bounded self-recursive calls
(e.g. `fib`, `ackermann`, `tak`), shifting all callee virtual registers above
`nextFreshVReg caller` and splicing callee blocks + continuation block directly
after `callBlk` so every caller edge preserves its exact forward/backward clock
direction and no critical edges are created.

Soundness is proved directly via `PotentialForward` in
`IxCC.Lir.Proof.Opt.Inline` (`inlineCallSite_sim : Sem.Sim Eq (fun k => 2 * k + 1)`).
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word)

/-! ## Callee register shifting and term rewriting -/

def shiftArg (off : VReg) : Arg → Arg
  | .v x => .v (off + x)
  | .imm w => .imm w

def shiftBase (off : VReg) : Base → Base
  | .v x => .v (off + x)
  | .ctx => .ctx

def shiftAddr (off : VReg) (m : Addr) : Addr :=
  { m with
    base := m.base.map (shiftBase off)
    index := m.index.map fun (x, s) => (off + x, s) }

def shiftRhs (off : VReg) : Rhs → Rhs
  | .arg a => .arg (shiftArg off a)
  | .bin o w a b => .bin o w (shiftArg off a) (shiftArg off b)
  | .load w e m => .load w e (shiftAddr off m)
  | .addr m => .addr (shiftAddr off m)
  | .select c w a b t f =>
      .select c w (shiftArg off a) (shiftArg off b) (shiftArg off t) (shiftArg off f)
  | .test c w a b => .test c w (shiftArg off a) (shiftArg off b)
  | .bsr64 a => .bsr64 (shiftArg off a)

def shiftLimb (off : VReg) : LimbOp → LimbOp
  | .mulWide64 a b => .mulWide64 (shiftArg off a) (shiftArg off b)
  | .divWide64 hi lo d => .divWide64 (shiftArg off hi) (shiftArg off lo) (shiftArg off d)
  | .addCarry64 a b c => .addCarry64 (shiftArg off a) (shiftArg off b) (shiftArg off c)
  | .subBorrow64 a b c => .subBorrow64 (shiftArg off a) (shiftArg off b) (shiftArg off c)

def shiftStmt (off : VReg) : Stmt → Stmt
  | .assign x r => .assign (off + x) (shiftRhs off r)
  | .limb r1 r2 op => .limb (off + r1) (off + r2) (shiftLimb off op)
  | .store w m a => .store w (shiftAddr off m) (shiftArg off a)
  | .call rs f as => .call (rs.map (off + ·)) f (as.map (shiftArg off))

def shiftEdge (off : VReg) (baseLbl : Label) (e : Edge) : Edge :=
  { target := baseLbl + e.target, args := e.args.map (shiftArg off) }

def rewriteCalleeTerm (off : VReg) (baseLbl contLbl : Label) : Term → Term
  | .jump e => .jump (shiftEdge off baseLbl e)
  | .br c w a b t f =>
      .br c w (shiftArg off a) (shiftArg off b)
        (shiftEdge off baseLbl t) (shiftEdge off baseLbl f)
  | .brOvf o x a b ok ovf =>
      .brOvf o (off + x) (shiftArg off a) (shiftArg off b)
        (shiftEdge off baseLbl ok) (shiftEdge off baseLbl ovf)
  | .ret as => .jump { target := contLbl, args := as.map (shiftArg off) }
  | .tail f as => .tail f (as.map (shiftArg off))
  | .fail r => .fail r
  | .trap => .trap

def rewriteTailCalleeTerm (off : VReg) (baseLbl : Label) : Term → Term
  | .jump e => .jump (shiftEdge off baseLbl e)
  | .br c w a b t f =>
      .br c w (shiftArg off a) (shiftArg off b)
        (shiftEdge off baseLbl t) (shiftEdge off baseLbl f)
  | .brOvf o x a b ok ovf =>
      .brOvf o (off + x) (shiftArg off a) (shiftArg off b)
        (shiftEdge off baseLbl ok) (shiftEdge off baseLbl ovf)
  | .ret as => .ret (as.map (shiftArg off))
  | .tail f as => .tail f (as.map (shiftArg off))
  | .fail r => .fail r
  | .trap => .trap

/-! ## Caller label remapping -/

def remapCallerLabel (callBlk delta : Label) (L : Label) : Label :=
  if L ≤ callBlk then L else L + delta

def remapCallerEdge (callBlk delta : Label) (e : Edge) : Edge :=
  { e with target := remapCallerLabel callBlk delta e.target }

def remapCallerTerm (callBlk delta : Label) : Term → Term
  | .jump e => .jump (remapCallerEdge callBlk delta e)
  | .br c w a b t f =>
      .br c w a b (remapCallerEdge callBlk delta t) (remapCallerEdge callBlk delta f)
  | .brOvf o x a b ok ovf =>
      .brOvf o x a b (remapCallerEdge callBlk delta ok) (remapCallerEdge callBlk delta ovf)
  | t => t

/-! ## Decidable register-bound and callee preconditions -/

def listLt (off : VReg) (xs : List VReg) : Bool :=
  xs.all fun x => decide (x < off)

def blockRegsLt (off : VReg) (b : Block) : Bool :=
  listLt off b.params &&
  b.body.toList.all (fun s => listLt off s.uses && listLt off s.defs) &&
  listLt off b.term.uses && listLt off b.term.defs && listLt off b.term.edgeUses

def funcRegsLt (F : Func) (off : VReg) : Bool :=
  listLt off F.params && F.blocks.toList.all (blockRegsLt off)

def calleeBlockOk (nBlocks nRes : Nat) (b : Block) : Bool :=
  (match b.term with
   | .ret as => as.length == nRes
   | _ => true) &&
  b.term.edges.all (fun e => e.target != 0 && decide (e.target < nBlocks))

def calleeInlineOk (callee : Func) (nArgs nRes : Nat) : Bool :=
  match callee.blocks[0]? with
  | none => false
  | some b0 =>
      b0.params.isEmpty &&
      nArgs == callee.params.length &&
      nRes == callee.results &&
      callee.blocks.toList.all (calleeBlockOk callee.blocks.size callee.results)

/-! ## Single-site call inlining transformation -/

/-- Fresh destination registers allocated for an inlined callee block `j` that ends in `.tail`. -/
def inlineTailFreshRs (callee : Func) (rs : List VReg) (off : VReg) (j : Nat) : List VReg :=
  let tailBase := off + nextFreshVReg callee + j * rs.length
  (List.range rs.length).map (tailBase + ·)

/-- Rewrite callee block `j` for splicing at `callBlk + 1 + j` with continuation `callBlk + M + 1`.
If the block ends in `.tail g tas`, the tail call becomes a normal `.call freshRs g (shift tas)`
followed by `.jump contLbl (freshRs)` so tail-recursive callees (`ackermann`, `tak`) inline cleanly. -/
def inlineCalleeBlock (callee : Func) (callBlk : Label) (blk : Block)
    (rs : List VReg) (off : VReg) (j : Nat) (b : Block) : Block :=
  let baseLbl := callBlk + 1
  let contLbl := callBlk + (callee.blocks.size + 1)
  let params' := if j == 0 then callee.params.map (off + ·) else b.params.map (off + ·)
  let body0 := b.body.map (shiftStmt off)
  match b.term with
  | .tail g tas =>
      let freshRs := inlineTailFreshRs callee rs off j
      { params := params'
        body := body0.push (.call freshRs g (tas.map (shiftArg off)))
        term := .jump { target := contLbl, args := freshRs.map .v }
        cold := b.cold || blk.cold }
  | t =>
      { params := params'
        body := body0
        term := rewriteCalleeTerm off baseLbl contLbl t
        cold := b.cold || blk.cold }

/-- Build the inlined caller function by splicing `callee` + continuation block directly
after `callBlk` (shifting all callee registers by `off`). -/
def buildInlinedFunc (caller callee : Func) (callBlk callPos : Label)
    (blk : Block) (rs : List VReg) (as : List Arg) (off : VReg) : Func :=
  let M := callee.blocks.size
  let delta := M + 1
  let baseLbl := callBlk + 1
  let prefixBlks : List Block :=
    (caller.blocks.toList.take callBlk).map fun b =>
      { b with term := remapCallerTerm callBlk delta b.term }
  let callBlk' : Block :=
    { blk with
      body := (blk.body.toList.take callPos).toArray
      term := .jump { target := baseLbl, args := as } }
  let inlinedBlks : List Block :=
    callee.blocks.toList.zipIdx.map fun (b, j) =>
      inlineCalleeBlock callee callBlk blk rs off j b
  let contBlk : Block :=
    { params := rs
      body := (blk.body.toList.drop (callPos + 1)).toArray
      term := remapCallerTerm callBlk delta blk.term
      cold := blk.cold }
  let suffixBlks : List Block :=
    (caller.blocks.toList.drop (callBlk + 1)).map fun b =>
      { b with term := remapCallerTerm callBlk delta b.term }
  { caller with blocks := (prefixBlks ++ [callBlk'] ++ inlinedBlks ++ [contBlk] ++ suffixBlks).toArray }

/-- Inline the `.call rs gi as` at `(fi, callBlk, callPos)` in `p` if all soundness
preconditions hold, returning `none` otherwise. -/
def inlineCallSite (p : Program) (fi : FunId) (callBlk callPos : Nat) : Option Program :=
  match p.funcs[fi]? with
  | none => none
  | some caller =>
      match caller.blocks[callBlk]? with
      | none => none
      | some blk =>
          match blk.body[callPos]? with
          | some (.call rs gi as) =>
              match p.funcs[gi]? with
              | none => none
              | some callee =>
                  let off := nextFreshVReg caller
                  if funcRegsLt caller off && calleeInlineOk callee as.length rs.length then
                    let caller' := buildInlinedFunc caller callee callBlk callPos blk rs as off
                    some { p with funcs := p.funcs.set! fi caller' }
                  else none
          | _ => none

/-- Checked single-site inline: applies `inlineCallSite` only when the resulting program
remains `WellFormed` (whenever `p` was `WellFormed`). Returns `(p', changed)`. -/
def inlineCallSiteChecked (p : Program) (fi : FunId) (callBlk callPos : Nat) : Program × Bool :=
  match inlineCallSite p fi callBlk callPos with
  | none => (p, false)
  | some q =>
      if !p.wellFormed || q.wellFormed then (q, true) else (p, false)

/-! ## Single-site `.tail` call inlining (`inlineTailSite`) -/

/-- Rewrite callee block `j` for tail-call splicing at `tailBlk + 1 + j`. -/
def inlineTailCalleeBlock (callee : Func) (tailBlk : Label) (blk : Block)
    (off : VReg) (j : Nat) (b : Block) : Block :=
  { params := if j == 0 then callee.params.map (off + ·) else b.params.map (off + ·)
    body := b.body.map (shiftStmt off)
    term := rewriteTailCalleeTerm off (tailBlk + 1) b.term
    cold := b.cold || blk.cold }

/-- Splice `callee` directly after `tailBlk`, replacing `tailBlk`'s `.tail gi as`
with `.jump ⟨tailBlk + 1, as⟩`. -/
def buildTailInlinedFunc (caller callee : Func) (tailBlk : Label)
    (blk : Block) (as : List Arg) (off : VReg) : Func :=
  let M := callee.blocks.size
  let baseLbl := tailBlk + 1
  let prefixBlks : List Block :=
    (caller.blocks.toList.take tailBlk).map fun b =>
      { b with term := remapCallerTerm tailBlk M b.term }
  let tailBlk' : Block :=
    { blk with term := .jump { target := baseLbl, args := as } }
  let inlinedBlks : List Block :=
    callee.blocks.toList.zipIdx.map fun (b, j) =>
      inlineTailCalleeBlock callee tailBlk blk off j b
  let suffixBlks : List Block :=
    (caller.blocks.toList.drop (tailBlk + 1)).map fun b =>
      { b with term := remapCallerTerm tailBlk M b.term }
  { caller with blocks := (prefixBlks ++ [tailBlk'] ++ inlinedBlks ++ suffixBlks).toArray }

/-- Inline a `.tail gi as` terminator at `(fi, tailBlk)` if all soundness preconditions hold. -/
def inlineTailSite (p : Program) (fi : FunId) (tailBlk : Label) : Option Program :=
  match p.funcs[fi]? with
  | none => none
  | some caller =>
      match caller.blocks[tailBlk]? with
      | none => none
      | some blk =>
          match blk.term with
          | .tail gi as =>
              match p.funcs[gi]? with
              | none => none
              | some callee =>
                  let off := nextFreshVReg caller
                  if funcRegsLt caller off && calleeInlineOk callee as.length caller.results then
                    let caller' := buildTailInlinedFunc caller callee tailBlk blk as off
                    some { p with funcs := p.funcs.set! fi caller' }
                  else none
          | _ => none

/-- Checked single-site tail-call inline preserving `WellFormed`. -/
def inlineTailSiteChecked (p : Program) (fi : FunId) (tailBlk : Label) : Program × Bool :=
  match inlineTailSite p fi tailBlk with
  | none => (p, false)
  | some q =>
      if !p.wellFormed || q.wellFormed then (q, true) else (p, false)

/-! ## Heuristic site selection (non-recursive helpers + bounded self-recursion) -/

private def funcStmtCount (F : Func) : Nat :=
  F.blocks.foldl (fun acc b => acc + b.body.size) 0

private def funcHasStore (F : Func) : Bool :=
  F.blocks.any fun b => b.body.any fun | .store .. => true | _ => false

private def funcHasRet (F : Func) : Bool :=
  F.blocks.any fun b => match b.term with | .ret _ => true | _ => false

private def funcCallsFun (F : Func) (g : FunId) : Bool :=
  F.blocks.any fun b =>
    b.body.any (fun | .call _ g' _ => g' == g | _ => false) ||
    match b.term with | .tail g' _ => g' == g | _ => false

/-- Set of blocks belonging to any natural loop in `F`. -/
private def loopBlockSet (F : Func) : Src.NatSet :=
  let n := F.blocks.size
  if n == 0 then .leaf
  else
    let doms := F.dominators
    let preds := F.preds
    (List.range n).foldl (init := .leaf) fun acc h =>
      let backSrcs := (preds[h]!).filter fun b => Lir.Func.dominates doms h b
      if backSrcs.isEmpty then acc
      else
        let nodes := naturalLoopNodes n preds h backSrcs
        nodes.toList.foldl (fun s (b, _) => s.insert b) acc

/-- Find the next eligible non-recursive helper call site `(fi, blk, pos)` in `p`. -/
def findHelperCallSite (p : Program) (fi : FunId) : Option (Nat × Nat) :=
  match p.funcs[fi]? with
  | none => none
  | some caller =>
      let inLoop := loopBlockSet caller
      (List.range caller.blocks.size).findSome? fun b =>
        match caller.blocks[b]? with
        | none => none
        | some blk =>
            if blk.cold then none
            else
              blk.body.toList.zipIdx.findSome? fun (s, pos) =>
                match s with
                | .call rs gi as =>
                    if gi == fi then none
                    else match p.funcs[gi]? with
                    | none => none
                    | some callee =>
                        let hot := inLoop.contains b
                        let smallEnough :=
                          if hot then callee.blocks.size ≤ 20 && funcStmtCount callee ≤ 60
                          else callee.blocks.size ≤ 4 && funcStmtCount callee ≤ 12
                        if smallEnough &&
                           caller.blocks.size + callee.blocks.size + 1 ≤ 120 &&
                           !funcCallsFun callee gi &&
                           !funcHasStore callee &&
                           funcHasRet callee &&
                           calleeInlineOk callee as.length rs.length then
                          some (b, pos)
                        else none
                | _ => none

/-- Find a non-recursive `.tail gi as` call site in `fi` (e.g. entry wrapper `f0(v0): tail f1(v0, 1, 1)`)
to expose constant odd initial arguments directly to the loop body. -/
def findTailHelperSite (p : Program) (fi : FunId) : Option Label :=
  match p.funcs[fi]? with
  | none => none
  | some caller =>
      let isWrapper := caller.blocks.size ≤ 2
      (List.range caller.blocks.size).findSome? fun b =>
        match caller.blocks[b]? with
        | none => none
        | some blk =>
            if blk.cold then none
            else match blk.term with
            | .tail gi as =>
                if gi == fi then none
                else match p.funcs[gi]? with
                | none => none
                | some callee =>
                    let smallEnough :=
                      if isWrapper then callee.blocks.size ≤ 60 && funcStmtCount callee ≤ 160
                      else callee.blocks.size ≤ 8 && funcStmtCount callee ≤ 24
                    if smallEnough &&
                       caller.blocks.size + callee.blocks.size ≤ 120 &&
                       !funcCallsFun callee gi &&
                       !funcCallsFun callee fi &&
                       !funcHasStore callee &&
                       funcHasRet callee &&
                       calleeInlineOk callee as.length caller.results then
                      some b
                    else none
            | _ => none

private def countSelfCalls (F : Func) (fi : FunId) : Nat :=
  F.blocks.foldl (init := 0) fun acc blk =>
    acc + blk.body.foldl (init := 0) fun n s =>
      match s with | .call _ gi _ => if gi == fi then n + 1 else n | _ => n

/-- Find a non-cold self-recursive call site `(blk, pos)` in `F` for bounded self-inlining.
Restricts to low-arity (`≤ 2` params) small scalar recursive functions (`fib`, `ackermann`),
avoiding register-spill bloat on 4-call/4-param functions (`tak`). When `pickLast = true`,
scans blocks/statements in reverse order so multi-call functions like `fib(n-2) + fib(n-1)`
peel both arms in a balanced way instead of unrolling only the first arm deeply. -/
def findSelfCallSite (p : Program) (fi : FunId) (maxBlocks : Nat) (pickLast : Bool := false) :
    Option (Nat × Nat) :=
  match p.funcs[fi]? with
  | none => none
  | some F =>
      let nCalls := countSelfCalls F fi
      let cap := if nCalls ≤ 1 then maxBlocks else min maxBlocks 56
      if F.params.length > 2 || F.blocks.size > 48 || funcStmtCount F > 140 ||
         funcHasStore F || !funcHasRet F then
        none
      else if F.blocks.size ≤ 12 && nCalls > 2 then
        none
      else if F.blocks.size + F.blocks.size + 1 > cap then
        none
      else
        let blkOrder := if pickLast then (List.range F.blocks.size).reverse else List.range F.blocks.size
        blkOrder.findSome? fun b =>
          match F.blocks[b]? with
          | none => none
          | some blk =>
              if blk.cold then none
              else
                let stmtOrder := if pickLast then blk.body.toList.zipIdx.reverse else blk.body.toList.zipIdx
                stmtOrder.findSome? fun (s, pos) =>
                  match s with
                  | .call rs gi as =>
                      if gi == fi && calleeInlineOk F as.length rs.length then
                        some (b, pos)
                      else none
                  | _ => none

end IxCC.Lir.Opt
