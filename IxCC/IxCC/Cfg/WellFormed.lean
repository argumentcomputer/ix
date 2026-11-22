import IxCC.Cfg.Syntax

/-! # Cfg well-formedness

`Cfg.WellFormed P`, decided by `Cfg.check`, which names
the first violation. Per function:

* block 0 exists and its parameters match the signature;
* every edge targets a block with as many parameters as it has arguments;
  a **forward edge goes to a higher label and a back edge to a lower or
  equal one**, so the graph without back edges is acyclic (and the order is
  the one `Rt.lower` needs);
* every back edge targets a block that dominates its source (dominators
  over forward edges; back edges then change none);
* **SSA with dominance:** each variable is defined once (block parameters
  and instruction results), below the function's supply, and every use is a
  parameter of its block, defined earlier in the block, or defined in a
  block that strictly dominates it;
* calls and tail calls name a function with the right arity; allocations
  carry `CtorInfo.ofKey` of their key and that many arguments; projections
  and `switch` keys come from the table, and a `switch`'s keys are distinct.

Blocks no forward path reaches (dead join points) are allowed and counted
by `unreachable`; their uses are not checked. Critical edges are allowed.
Not on the recheck path (it is `Cfg.lower`'s postcondition). -/

namespace IxCC.Cfg

open IxCC.Fir (Var FunId Arg)
open IxCC.Src (NatSet)

namespace Check

def argVars : List Arg → List Var
  | [] => []
  | .var x :: as => x :: argVars as
  | _ :: as => argVars as

def rhsVars : Own.Rhs → List Var
  | .fir (.arg a) => argVars [a]
  | .fir (.ctor _ as) | .fir (.prim _ as) | .fir (.call _ as) | .alloc _ as _ => argVars as
  | .fir (.proj x ..) | .proj x .. => [x]

def termVars : Term → List Var
  | .jump e => argVars e.args
  | .switch x alts d => x :: (alts.map (·.2) ++ d.toList).flatMap (argVars ·.args)
  | .ret a => argVars [a]
  | .tcall _ as => argVars as
  | .trap => []

def instrDefs (b : Block) : List Var := b.body.map fun | .bind x _ => x

def blockDefs (b : Block) : List Var := b.params.map (·.1) ++ instrDefs b

def entryArity (P : Program) (f : FunId) : Option Nat :=
  (P.fun? f).bind fun fd => (fd.block? 0).map (·.params.length)

def rhsOk (P : Program) : Own.Rhs → Except String Unit
  | .fir (.arg _) => .ok ()
  | .fir (.prim p as) => if as.length == p.arity then .ok () else .error s!"{p.name} unsaturated"
  | .fir (.call f as) =>
    if entryArity P f == some as.length then .ok () else .error s!"call of f{f} with {as.length}"
  | .fir (.ctor ..) | .fir (.proj ..) => .error "a Fir ctor or proj in Cfg"
  | .alloc c as _ =>
    if Fir.CtorInfo.ofKey P.ctors c.key != some c then .error "alloc info is not ofKey"
    else if as.length != c.arity then .error "alloc arity" else .ok ()
  | .proj _ c i =>
    match Fir.CtorInfo.ofKey P.ctors c with
    | some info => if i < info.arity then .ok () else .error "projection index"
    | none => .error "projection key not in the table"

/-- Forward predecessors of block `i`. -/
def preds (fd : Fun) (i : BlockId) : List BlockId :=
  (List.range fd.blocks.length).filter fun p =>
    match fd.block? p with
    | some b => b.term.edges.any fun e => !e.back && e.target == i
    | none => false

/-- Dominator sets (ascending lists) of the blocks, over forward edges;
`none` for a block no forward path reaches. Forward edges go up, so one pass
in label order suffices. -/
def dominators (fd : Fun) : List (Option (List BlockId)) :=
  (List.range fd.blocks.length).foldl (fun (doms : List (Option (List BlockId))) i =>
    if i == 0 then doms ++ [some [0]]
    else
      let ps := (preds fd i).filterMap fun p => (doms[p]?).join
      match ps with
      | [] => doms ++ [none]
      | d :: ds => doms ++ [some ((ds.foldl (fun acc s => acc.filter (s.contains ·)) d) ++ [i])])
    []

end Check

open Check in
/-- One function. -/
def checkFun (P : Program) (f : FunId) (fd : Fun) : Except String Unit := do
  let n := fd.blocks.length
  let some entry := fd.block? 0 | throw s!"f{f}: no entry block"
  if entry.params.map (·.2) != fd.sig.params then throw s!"f{f}: entry parameters differ from the signature"
  -- single definition
  let defs := fd.blocks.flatMap blockDefs
  if !decide defs.Nodup then throw s!"f{f}: a variable is defined twice"
  if !(defs.all (· < fd.vars)) then throw s!"f{f}: a variable is beyond the supply {fd.vars}"
  let doms := dominators fd
  for i in List.range n do
    let some b := fd.block? i | throw s!"f{f}: block {i} missing"
    -- edges, label order, arities, back edges to dominators
    for e in b.term.edges do
      let some t := fd.block? e.target | throw s!"f{f} b{i}: edge to missing block {e.target}"
      if e.args.length != t.params.length then throw s!"f{f} b{i}: edge to b{e.target} arity"
      if e.back && e.target > i then throw s!"f{f} b{i}: back edge to a later block {e.target}"
      if !e.back && e.target ≤ i then throw s!"f{f} b{i}: forward edge to an earlier block {e.target}"
      if e.back then
        match (doms[i]?).join with
        | some d => if !d.contains e.target then throw s!"f{f} b{i}: back edge to a non-dominator b{e.target}"
        | none => pure ()
    match b.term with
    | .switch _ alts _ =>
      let ks := alts.map (·.1)
      if !decide ks.Nodup then throw s!"f{f} b{i}: switch keys repeat"
      if !(ks.all fun k => (Fir.CtorInfo.ofKey P.ctors k).isSome) then throw s!"f{f} b{i}: switch key not in the table"
    | .tcall g as =>
      if entryArity P g != some as.length then throw s!"f{f} b{i}: tail call of f{g} arity"
    | _ => pure ()
    for ins in b.body do
      match ins with
      | .bind _ r => (rhsOk P r).mapError (s!"f{f} b{i}: " ++ ·)
    -- dominance of uses
    match (doms[i]?).join with
    | some d =>
      let outer := (d.filter (· != i)).flatMap fun p => ((fd.block? p).map blockDefs).getD []
      let mut avail : NatSet := NatSet.ofList (outer ++ b.params.map (·.1))
      for ins in b.body do
        match ins with
        | .bind x r =>
          for y in rhsVars r do
            if !avail.contains y then throw s!"f{f} b{i}: v{y} used before its definition"
          avail := avail.insert x
      for y in termVars b.term do
        if !avail.contains y then throw s!"f{f} b{i}: v{y} used before its definition"
    | none => pure ()

/-- Well-formedness with the first violation. -/
def check (P : Program) : Except String Unit := do
  for f in List.range P.size do
    match P.fun? f with
    | some fd => checkFun P f fd
    | none => throw s!"f{f} is missing"
  if !decide (P.funList.map (·.2.key)).Nodup then throw "function keys repeat"
  if !(P.exports.all (· < P.size)) then throw "an export is out of range"

def wellFormed (P : Program) : Bool := (check P).isOk

def WellFormed (P : Program) : Prop := wellFormed P = true

instance (P : Program) : Decidable (WellFormed P) := inferInstanceAs (Decidable (_ = true))

/-- Blocks no forward path from the entry reaches. -/
def unreachable (P : Program) : Nat :=
  P.funList.foldl (fun n (_, fd) => n + ((Check.dominators fd).filter (·.isNone)).length) 0

/-- Back edges, over all functions. -/
def backEdges (P : Program) : Nat :=
  P.funList.foldl (fun n (_, fd) =>
    n + fd.blocks.foldl (fun m b => m + (b.term.edges.filter (·.back)).length) 0) 0

end IxCC.Cfg
