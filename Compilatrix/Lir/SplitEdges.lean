import Compilatrix.Lir.Graph

/-!
# Critical-edge splitting

A Lir pass that makes every edge non-critical (05 §2, `WellFormed`
condition 3). Cross-check S14 makes `Rt.lower` responsible for emitting
critical-edge-free Lir; this pass is the tool it (and the tests) use.

Each critical edge `b → s` with arguments `as` becomes `b → e` without
arguments and `e → s` with `as`, where `e` is a new empty block. The
arguments are read in `e` rather than `b`, in the same environment: `e`
defines nothing, and `brOvf`'s result is already bound on the edge.

**The clock is preserved exactly.** The new blocks of `b` are placed right
after `b` in label order and later labels shift up, so labels keep their
relative order. Then `b → e` is forward (free) and `e → s` is charged iff
`s ≤ b` in the old numbering, just as `b → s` was. `eval` therefore gives the
same outcome at every clock, which `check-lir` tests on generated programs.
-/

namespace Compilatrix.Lir

namespace Func

/-- The new label of each old block, from `label` on: its index plus the
split blocks before it (`offset` so far). -/
def newLabels : List Nat → Nat → Nat → List Label
  | [], _, _ => []
  | split :: splits, label, offset => (label + offset) :: newLabels splits (label + 1) (offset + split)

/-- A block's edges with each critical one redirected to its split block
(numbered from `first`), and the critical edges in order. -/
def splitEdges (critical : Edge → Bool) (relabel : Label → Label) (first : Label) :
    List Edge → List Edge → List Edge → List Edge × List Edge
  | [], edges, pending => (edges, pending)
  | e :: rest, edges, pending =>
    if critical e then
      splitEdges critical relabel first rest (edges ++ [{ target := first + pending.length, args := [] }])
        (pending ++ [e])
    else
      splitEdges critical relabel first rest (edges ++ [{ e with target := relabel e.target }]) pending

/-- Split every critical edge (see the module note). The entry keeps
label 0, and a function without critical edges is returned unchanged.
Kernel-evaluable style (M1.K1): the blocks are walked as a list, the
predecessor counts and labels are lists built once, and no array is
indexed. -/
def splitCriticalEdges (f : Func) : Func :=
  let blocks := f.blocks.toList
  let n := blocks.length
  let succs := blocks.flatMap (·.term.succs)
  let preds := (List.range n).map succs.count
  let critical (b : Block) (e : Edge) : Bool :=
    b.term.edges.length ≥ 2 && (preds[e.target]?.getD 0) ≥ 2
  let splits := blocks.map fun b => (b.term.edges.filter (critical b)).length
  if splits.all (· == 0) then f else
  let labels := newLabels splits 0 0
  let total := splits.sum
  let relabel (l : Label) : Label := if l < n then labels[l]?.getD l else l + total
  let rec emit : List Block → List Label → List Block
    | [], _ => []
    | block :: rest, label :: labels =>
      let (edges, pending) := splitEdges (critical block) relabel (label + 1) block.term.edges [] []
      ({ block with term := block.term.setEdges edges } ::
        pending.map fun e =>
          let targetCold := ((blocks[e.target]?).map (·.cold)).getD false
          { term := .jump { e with target := relabel e.target }, cold := block.cold || targetCold }) ++
        emit rest labels
    | _ :: _, [] => []
  { f with blocks := (emit blocks labels).toArray }

end Func

def Program.splitCriticalEdges (p : Program) : Program :=
  { p with funcs := p.funcs.map Func.splitCriticalEdges }

end Compilatrix.Lir
