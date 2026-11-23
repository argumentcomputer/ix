import IxCC.Cfg.Rc.Layout
import IxCC.Src.NatMap

/-! # Dead Reset/Reuse Wrapper Pruning (Track A4)

Replaces every uncalled `reset`/`resetU`/`reuse`/`reuseU` wrapper in
`(l.isUniqueProc, l.init + 4 + 4 * l.ctors.length)` with a 1-block 0-parameter
`.trap` stub after `Inline.inlineProgram` and before `splitCriticalEdges`.

Function indices, `main`, every source function, every core runtime procedure
(`inc`, `dec`, `alloc`, `init`, `natPow`, `natGcd`, `isUnique`), and every
called reset/reuse wrapper are preserved identically. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Prune

open IxCC.Cfg.Rc.Native

def stmtCallee (s : Lir.Stmt) (acc : Src.NatSet) : Src.NatSet :=
  match s with
  | .call _ g _ => acc.insert g
  | _ => acc

def termCallee (t : Lir.Term) (acc : Src.NatSet) : Src.NatSet :=
  match t with
  | .tail g _ => acc.insert g
  | _ => acc

def blockCallees (b : Lir.Block) (acc : Src.NatSet) : Src.NatSet :=
  termCallee b.term (b.body.toList.foldl (fun m s => stmtCallee s m) acc)

def funcCallees (F : Lir.Func) (acc : Src.NatSet) : Src.NatSet :=
  F.blocks.toList.foldl (fun m b => blockCallees b m) acc

def calledBySources (sourceCount : Nat) (p : Lir.Program) : Src.NatSet :=
  (List.range sourceCount).foldl (fun acc fi =>
    match p.funcs[fi]? with
    | some F => funcCallees F acc
    | none => acc) .leaf

def isPrunableReuse (l : Layout) (i : Nat) : Bool :=
  decide (l.isUniqueProc < i ∧ i < l.init + 4 + 4 * l.ctors.length)

def pruneStub (F : Lir.Func) : Lir.Func :=
  { name := F.name, params := [], results := F.results, blocks := #[{ term := .trap }] }

def pruneUnusedReuse (l : Layout) (p : Lir.Program) : Lir.Program :=
  let used := calledBySources l.sourceCount p
  { p with
    funcs := p.funcs.mapIdx fun i F =>
      if isPrunableReuse l i && !used.contains i then pruneStub F else F }

end IxCC.Cfg.Rc.Prune
