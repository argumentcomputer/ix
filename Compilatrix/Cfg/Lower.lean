import Compilatrix.Cfg.Syntax
import Compilatrix.Own.Immortal
import Compilatrix.Fir.Lower

/-! # Own → Cfg (`Cfg.lower`)

Design note 03 §7: structured Own code becomes blocks. Style P on the
recheck path (proved once, re-run, 03 §4.5), so kernel-evaluable (D17):
structural recursion, lists and `Src.NatMap`.

* Straight-line `bind`s go into the current block; a call stays an
  instruction (it returns to the next one).
* `jp j ps φ rec body k`: `k` continues the current block; the body is a new
  block whose parameters are `ps` (variables of the enclosing scope are
  visible by dominance: the block defining `j` dominates `j`'s block). A
  jump from `k` is a forward edge; a jump from `j`'s own body (recursive
  `j`) is a **back edge** (06 S30).
* `case x alts d` ends the block with a `switch`; each arm is a new block.
* A self `tcall` is a back edge to block 0 with the arguments as its
  parameters; other tail calls stay `tcall`s.
* Kinds, modes and constructor keys are carried for 04.

**Numbering.** Blocks are numbered so that every forward edge goes to a
higher label and every back edge to a lower or equal one: a join point's
block comes after every block of its scope `k` (which jumps to it) and
before the blocks of its body; a `case`'s arms come in order, each followed
by its own blocks. `count` gives the number of blocks a piece of code opens,
so labels are known before they are emitted. -/

namespace Compilatrix.Cfg

open Compilatrix.Fir (Var FunId JoinId Arg)

namespace Lower

mutual

/-- The blocks lowering `c` opens (besides the current one). -/
def count : Own.Code → Nat
  | .bind _ _ k => count k
  | .jp _ _ _ _ b k => count k + 1 + count b
  | .case _ alts d => countAlts alts + countOpt d
  | .jmp .. | .ret _ | .tcall .. | .trap => 0

def countAlts : List Own.Alt → Nat
  | [] => 0
  | .mk _ b :: as => 1 + count b + countAlts as

def countOpt : Option Own.Code → Nat
  | none => 0
  | some c => 1 + count c

end

/-- The `switch` edges of a `case`: arm `i` starts at `next` plus the blocks
of the arms before it. -/
def armEdges (next : BlockId) : List Own.Alt → List (Key.CtorKey × Edge)
  | [] => []
  | .mk key b :: as => (key, { target := next }) :: armEdges (next + 1 + count b) as

/-- Emitted blocks by label. -/
abbrev Out := Src.NatMap Block

/-- A join point in scope: its block, and whether a jump to it is a back
edge (inside its own body). -/
abbrev JScope := List (JoinId × BlockId × Bool)

def finish (out : Out) (cur : BlockId) (params : List (Var × Own.PSig)) (acc : List Instr)
    (t : Term) : Out :=
  out.insert cur { params, body := acc.reverse, term := t }

mutual

/-- Lower `c` into the current block `cur` (parameters `params`, body so far
`acc`, reversed); new blocks are numbered from `next`. -/
def code (self : FunId) (J : JScope) (cur : BlockId) (params : List (Var × Own.PSig))
    (acc : List Instr) (next : BlockId) (out : Out) : Own.Code → Out
  | .bind x r k => code self J cur params (.bind x r :: acc) next out k
  | .jp j ps _ r b k =>
    let bj := next + count k
    let out := code self ((j, bj, false) :: J) cur params acc next out k
    code self (if r then (j, bj, true) :: J else J) bj ps [] (bj + 1) out b
  | .jmp j as =>
    match J.lookup j with
    | some (bj, back) => finish out cur params acc (.jump { target := bj, args := as, back })
    | none => finish out cur params acc .trap
  | .case x alts d =>
    let edges := armEdges next alts
    let dnext := next + countAlts alts
    let dedge := d.map fun _ => ({ target := dnext } : Edge)
    let out := finish out cur params acc (.switch x edges dedge)
    let out := arms self J next out alts
    match d with
    | some c => code self J dnext [] [] (dnext + 1) out c
    | none => out
  | .ret a => finish out cur params acc (.ret a)
  | .tcall f as =>
    if f = self then finish out cur params acc (.jump { target := 0, args := as, back := true })
    else finish out cur params acc (.tcall f as)
  | .trap => finish out cur params acc .trap

/-- Each arm in a new block, in order. -/
def arms (self : FunId) (J : JScope) (next : BlockId) (out : Out) : List Own.Alt → Out
  | [] => out
  | .mk _ b :: as =>
    let out := code self J next [] [] (next + 1) out b
    arms self J (next + 1 + count b) out as

end

def function (f : FunId) (fd : Own.Fun) : Fun :=
  let out := code f [] 0 (fd.params.zip fd.sig.params) [] 1 .leaf fd.body
  { key := fd.key, sig := fd.sig, regionFrame := fd.regionFrame, vars := fd.vars
    blocks := (List.range (1 + count fd.body)).map fun b => out.getD b { term := .trap } }

end Lower

/-- Own → Cfg (03 §7). -/
def lower (q : Own.Program) : Program :=
  { funs := Src.NatMap.ofList (q.funList.map fun (f, fd) => (f, Lower.function f fd))
    size := q.size, exports := q.exports, ctors := q.ctors, known := q.known }

/-- The Phase 1 path from Anf: `Fir.lower`, then `Own.immortal`, then
`Cfg.lower` (all style P, re-run on the recheck path). -/
def ofAnf (A : Anf.Program) : Except Fir.Lower.Error Program :=
  (Fir.lower A).map fun p => lower (Own.immortal p)

end Compilatrix.Cfg
