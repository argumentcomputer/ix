import IxCC.Lir.Graph
import Std.Data.HashMap

/-!
# Well-formed Lir

The decidable conditions the allocator and layout rely on (05 §2). Validator
soundness does not need them, and neither does the semantics.

1. `main` and every called function exist, with matching arities: call
   arguments and results, tail-call arguments and results, `ret` values and
   edge arguments against block parameters.
2. The entry block has no parameters and no predecessors.
3. No critical edges: an edge whose source has several outgoing edges never
   enters a block with several incoming edges (counted with multiplicity).
4. Every block is reachable from the entry.
5. SSA: each register is defined once (function parameters, block
   parameters, statement and call results, `brOvf` results), and each
   definition dominates its uses. Within a block the order is: parameters,
   then each statement's uses before its definitions, then the terminator's
   operands, its definition, and the edge arguments (so edge arguments may
   read `brOvf`'s result).
6. Every displacement fits a signed 32-bit field.
7. No `Base.ctx` store reaches the context's `entrySp` or `stackLimit` cell
   (`ctx − 64`, `ctx − 56`), which the failure exit and the prologue read
   (05 §6.1). Without an index the store's bytes `[disp, disp + w)` must miss
   `[−64, −48)`; with an index the displacement must be at least −48. (That
   an index does not wrap, and that stores through registers stay in the
   heap, are runtime invariants, not syntax.)

`Program.check` names the first violation.
-/

namespace IxCC.Lir

def fitsI32 (d : Int) : Bool := decide (-2147483648 ≤ d ∧ d < 2147483648)

/-- A `Base.ctx` store of `bytes` bytes that may write `entrySp` or
`stackLimit` (condition 7). -/
def Addr.hitsProtectedCtx (m : Addr) (bytes : Nat) : Bool :=
  m.base == some .ctx && decide (m.disp < -48) &&
    (m.index.isSome || decide (-64 < m.disp + bytes))

/-- Position of a definition or use within its block (see the module note). -/
private def paramPos : Nat := 0
private def stmtUsePos (i : Nat) : Nat := 2 * i + 1
private def stmtDefPos (i : Nat) : Nat := 2 * i + 2
private def termUsePos (b : Block) : Nat := 2 * b.body.size + 1
private def termDefPos (b : Block) : Nat := 2 * b.body.size + 2
private def edgeUsePos (b : Block) : Nat := 2 * b.body.size + 3

namespace Func

private def site (fi : FunId) (f : Func) (b : Label) : String :=
  s!"function {fi}{if f.name.isEmpty then "" else s!" ({f.name})"} block {b}"

/-- Structure, arities and displacements (conditions 1–3 and 6). -/
def checkShape (p : Program) (fi : FunId) (f : Func) : Except String Unit := do
  let n := f.blocks.size
  if n == 0 then throw s!"function {fi} has no blocks"
  unless f.blocks[0]!.params.isEmpty do throw s!"{site fi f 0}: the entry block has parameters"
  let preds := f.predCounts
  for h : b in [:n] do
    let block := f.blocks[b]
    let edges := block.term.edges
    for e in edges do
      match f.blocks[e.target]? with
      | none => throw s!"{site fi f b}: edge to missing block {e.target}"
      | some target =>
          if e.target == 0 then throw s!"{site fi f b}: edge to the entry block"
          unless e.args.length == target.params.length do
            throw s!"{site fi f b}: edge to block {e.target} passes {e.args.length} arguments for {target.params.length} parameters"
          if edges.length ≥ 2 && preds[e.target]! ≥ 2 then
            throw s!"{site fi f b}: critical edge to block {e.target}"
    for h : i in [:block.body.size] do
      let stmt := block.body[i]
      for m in stmt.addrs do
        unless fitsI32 m.disp do throw s!"{site fi f b} statement {i}: displacement {m.disp} does not fit i32"
      if let .store w m _ := stmt then
        if m.hitsProtectedCtx w.bytes then
          throw s!"{site fi f b} statement {i}: store may reach the context's entrySp or stackLimit cell"
      if let .call rs g as := stmt then
        match p.funcs[g]? with
        | none => throw s!"{site fi f b} statement {i}: call to missing function {g}"
        | some callee =>
            unless as.length == callee.params.length do
              throw s!"{site fi f b} statement {i}: call to {g} passes {as.length} arguments for {callee.params.length}"
            unless rs.length == callee.results do
              throw s!"{site fi f b} statement {i}: call to {g} binds {rs.length} results of {callee.results}"
    match block.term with
    | .ret as =>
        unless as.length == f.results do
          throw s!"{site fi f b}: returns {as.length} values of {f.results}"
    | .tail g as =>
        match p.funcs[g]? with
        | none => throw s!"{site fi f b}: tail call to missing function {g}"
        | some callee =>
            unless as.length == callee.params.length do
              throw s!"{site fi f b}: tail call to {g} passes {as.length} arguments for {callee.params.length}"
            unless callee.results == f.results do
              throw s!"{site fi f b}: tail call to {g} returns {callee.results} values of {f.results}"
    | _ => pure ()

/-- Unique definitions dominating their uses (conditions 4 and 5). -/
def checkSsa (fi : FunId) (f : Func) : Except String Unit := do
  let n := f.blocks.size
  let order := f.rpo
  unless order.size == n do
    let reachable := f.rpoIndex
    let missing := (List.range n).filter fun b => (reachable[b]!).isNone
    throw s!"function {fi}: unreachable blocks {missing}"
  let mut defs : Std.HashMap VReg (Label × Nat) := {}
  let define (defs : Std.HashMap VReg (Label × Nat)) (x : VReg) (b pos : Nat) :
      Except String (Std.HashMap VReg (Label × Nat)) :=
    if defs.contains x then throw s!"{site fi f b}: v{x} is defined twice" else pure (defs.insert x (b, pos))
  for x in f.params do defs ← define defs x 0 paramPos
  for h : b in [:n] do
    let block := f.blocks[b]
    for x in block.params do defs ← define defs x b paramPos
    for h : i in [:block.body.size] do
      for x in block.body[i].defs do defs ← define defs x b (stmtDefPos i)
    for x in block.term.defs do defs ← define defs x b (termDefPos block)
  let doms := f.dominators
  let check (b pos : Nat) (x : VReg) : Except String Unit :=
    match defs[x]? with
    | none => throw s!"{site fi f b}: v{x} is used but never defined"
    | some (db, dpos) =>
        if (db == b && dpos < pos) || (db != b && dominates doms db b) then pure ()
        else throw s!"{site fi f b}: the definition of v{x} (block {db}) does not dominate its use"
  for h : b in [:n] do
    let block := f.blocks[b]
    for h : i in [:block.body.size] do
      for x in block.body[i].uses do check b (stmtUsePos i) x
    for x in block.term.uses do check b (termUsePos block) x
    for x in block.term.edgeUses do check b (edgeUsePos block) x

end Func

def Program.check (p : Program) : Except String Unit := do
  unless p.main < p.funcs.size do throw s!"main function {p.main} is missing"
  for h : fi in [:p.funcs.size] do
    p.funcs[fi].checkShape p fi
    p.funcs[fi].checkSsa fi

def Program.wellFormed (p : Program) : Bool := p.check.toBool

/-- Well-formed Lir (decidable). -/
def WellFormed (p : Program) : Prop := p.wellFormed = true

instance (p : Program) : Decidable (WellFormed p) := inferInstanceAs (Decidable (_ = true))

end IxCC.Lir
