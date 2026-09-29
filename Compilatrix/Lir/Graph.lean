import Compilatrix.Lir.Syntax

/-!
# Lir control-flow graphs

Successors, predecessor counts (with multiplicity: a `br` whose two edges
reach one block counts twice), reverse postorder from the entry, and
dominator sets. `WellFormed` uses them for the SSA and critical-edge checks;
the allocator will use them for liveness and ordering.

Dominator sets are bitsets (`Nat`) computed by the iterative data-flow
equations in reverse postorder. Each pass that changes something removes at
least one bit, so `n² + 2` passes always reach the fixpoint.
-/

namespace Compilatrix.Lir

namespace Func

def succs (f : Func) (b : Label) : List Label :=
  match f.blocks[b]? with
  | some block => block.term.succs
  | none => []

/-- The number of edges leaving each block. -/
def succCount (f : Func) (b : Label) : Nat := (f.succs b).length

def edgeCount (f : Func) : Nat := f.blocks.foldl (fun n b => n + b.term.edges.length) 0

/-- The number of edges entering each block (targets out of range ignored). -/
def predCounts (f : Func) : Array Nat :=
  f.blocks.foldl (init := Array.replicate f.blocks.size 0) fun counts b =>
    b.term.succs.foldl (init := counts) fun counts s =>
      if s < counts.size then counts.modify s (· + 1) else counts

/-- Predecessor labels of each block, in ascending order with multiplicity. -/
def preds (f : Func) : Array (List Label) := Id.run do
  let mut preds := Array.replicate f.blocks.size ([] : List Label)
  for h : b in [:f.blocks.size] do
    for s in f.blocks[b].term.succs do
      if s < preds.size then preds := preds.modify s (b :: ·)
  return preds.map List.reverse

/-- Depth-first postorder of the blocks reachable from the entry. -/
def postorder (f : Func) : Array Label :=
  let n := f.blocks.size
  if n == 0 then #[] else
  let rec loop (fuel : Nat) (stack : List (Label × List Label)) (visited : Array Bool)
      (post : Array Label) : Array Label :=
    match fuel, stack with
    | 0, _ | _, [] => post
    | fuel + 1, (b, []) :: rest => loop fuel rest visited (post.push b)
    | fuel + 1, (b, s :: ss) :: rest =>
        if s < n && !visited[s]! then
          loop fuel ((s, f.succs s) :: (b, ss) :: rest) (visited.set! s true) post
        else
          loop fuel ((b, ss) :: rest) visited post
  loop (2 * n + f.edgeCount + 1) [(0, f.succs 0)] ((Array.replicate n false).set! 0 true) #[]

/-- Reverse postorder: the entry first, each block before its forward
successors. -/
def rpo (f : Func) : Array Label := f.postorder.reverse

/-- Position of each block in `rpo`; `none` for unreachable blocks. -/
def rpoIndex (f : Func) : Array (Option Nat) := Id.run do
  let mut index := Array.replicate f.blocks.size none
  for h : i in [:f.rpo.size] do
    let b := f.rpo[i]
    if b < index.size then index := index.set! b (some i)
  return index

/-- `doms[b]` has bit `d` set iff `d` dominates `b` (reflexively). Unreachable
blocks have the empty set. -/
def dominators (f : Func) : Array Nat :=
  let n := f.blocks.size
  if n == 0 then #[] else
  let order := f.rpo
  let reachable := f.rpoIndex.map Option.isSome
  let preds := f.preds
  let full := 2 ^ n - 1
  let init := (Array.range n).map fun b =>
    if b == 0 then 1 else if reachable[b]! then full else 0
  let pass (doms : Array Nat) : Array Nat := Id.run do
    let mut doms := doms
    for b in order do
      if b != 0 then
        let meet := preds[b]!.foldl (init := full) fun acc p =>
          if reachable[p]! then acc &&& doms[p]! else acc
        doms := doms.set! b (meet ||| (1 <<< b))
    return doms
  let rec fix (fuel : Nat) (doms : Array Nat) : Array Nat :=
    match fuel with
    | 0 => doms
    | fuel + 1 =>
        let next := pass doms
        if next == doms then doms else fix fuel next
  fix (n * n + 2) init

/-- `d` dominates `b` in the sets `doms`. -/
def dominates (doms : Array Nat) (d b : Label) : Bool := (doms[b]?.getD 0).testBit d

/-- Immediate dominators: the strict dominator latest in reverse postorder
(strict dominators form a chain). `none` for the entry and unreachable
blocks. -/
def idoms (f : Func) : Array (Option Label) :=
  let doms := f.dominators
  let index := f.rpoIndex
  (Array.range f.blocks.size).map fun b =>
    (List.range f.blocks.size).foldl (init := none) fun best d =>
      if d != b && dominates doms d b then
        match best with
        | none => some d
        | some e => if (index[d]!.getD 0) > (index[e]!.getD 0) then some d else some e
      else best

end Func

/-- An edge is critical when its source has several outgoing edges and its
target several incoming ones. -/
def Func.criticalEdges (f : Func) : List (Label × Nat) := Id.run do
  let preds := f.predCounts
  let mut out := []
  for h : b in [:f.blocks.size] do
    let edges := f.blocks[b].term.edges
    if edges.length ≥ 2 then
      for (e, j) in edges.zipIdx do
        if (preds[e.target]?.getD 0) ≥ 2 then out := (b, j) :: out
  return out.reverse

end Compilatrix.Lir
