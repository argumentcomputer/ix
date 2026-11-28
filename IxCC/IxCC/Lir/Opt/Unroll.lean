import IxCC.Lir.Opt.Inline
import IxCC.Lir.Graph
import IxCC.Lir.WellFormed
import IxCC.Src.NatMap

/-!
# Directly-verified bounded loop unrolling and odd-fixnum loop versioning (`Lir.Opt.Unroll`)

Provides two composable, formally verified CFG loop transformations:
1. **`unrollLoopSite`**: unrolls a natural loop `(h, nodes)` by factor `U ≥ 2`,
   duplicating `nodes` and any leaf exit blocks (`ret`/`tail`/`fail`/`trap`) per
   unrolled copy with disjoint shifted registers and adding 0-stmt trampolines
   for non-leaf exits so zero critical edges are created.
   Proved directly via `PotentialForward` (`Sem.Sim Eq (fun k => U * k + (U - 1))`).
2. **`versionOddLoopSite`**: specializes a natural loop `(h, nodes)` on a header
   parameter `p = h.params[testParamIdx]` via a pre-loop `br .tnz p, 1` guard
   dispatching to a cloned fast loop copy (where `p` is provably odd on entry so
   subsequent `Lir.Opt.runLocal` eliminates `--bignat` tag checks and `brOvf`) or
   the original slow fallback loop.
   Proved directly via `Sem.Forward` (`Sem.Sim Eq id`).
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func Program Word)

/-! ## Loop register shifting -/

/-- Shift register `x` for loop copy `c`: copy `0` is identity; copies `c ≥ 1` shift
every register in `clonedDefs` to `c * off + x` and leave outer dominating registers fixed. -/
def loopMapReg (clonedDefs : Src.NatSet) (off c : Nat) (x : VReg) : VReg :=
  if c == 0 || !clonedDefs.contains x then x else c * off + x

def loopMapArg (clonedDefs : Src.NatSet) (off c : Nat) : Arg → Arg
  | .v x => .v (loopMapReg clonedDefs off c x)
  | .imm w => .imm w

def loopMapBase (clonedDefs : Src.NatSet) (off c : Nat) : Base → Base
  | .v x => .v (loopMapReg clonedDefs off c x)
  | .ctx => .ctx

def loopMapAddr (clonedDefs : Src.NatSet) (off c : Nat) (m : Addr) : Addr :=
  { m with
    base := m.base.map (loopMapBase clonedDefs off c)
    index := m.index.map fun (x, s) => (loopMapReg clonedDefs off c x, s) }

def loopMapRhs (clonedDefs : Src.NatSet) (off c : Nat) : Rhs → Rhs
  | .arg a => .arg (loopMapArg clonedDefs off c a)
  | .bin o w a b => .bin o w (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
  | .load w e m => .load w e (loopMapAddr clonedDefs off c m)
  | .addr m => .addr (loopMapAddr clonedDefs off c m)
  | .select cond w a b t f =>
      .select cond w (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
        (loopMapArg clonedDefs off c t) (loopMapArg clonedDefs off c f)
  | .test cond w a b =>
      .test cond w (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
  | .bsr64 a => .bsr64 (loopMapArg clonedDefs off c a)

def loopMapLimb (clonedDefs : Src.NatSet) (off c : Nat) : LimbOp → LimbOp
  | .mulWide64 a b => .mulWide64 (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
  | .divWide64 hi lo d =>
      .divWide64 (loopMapArg clonedDefs off c hi) (loopMapArg clonedDefs off c lo)
        (loopMapArg clonedDefs off c d)
  | .addCarry64 a b cin =>
      .addCarry64 (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
        (loopMapArg clonedDefs off c cin)
  | .subBorrow64 a b bin =>
      .subBorrow64 (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
        (loopMapArg clonedDefs off c bin)

def loopMapStmt (clonedDefs : Src.NatSet) (off c : Nat) : Stmt → Stmt
  | .assign x r => .assign (loopMapReg clonedDefs off c x) (loopMapRhs clonedDefs off c r)
  | .limb r1 r2 op =>
      .limb (loopMapReg clonedDefs off c r1) (loopMapReg clonedDefs off c r2)
        (loopMapLimb clonedDefs off c op)
  | .store w m a =>
      .store w (loopMapAddr clonedDefs off c m) (loopMapArg clonedDefs off c a)
  | .call rs f as =>
      .call (rs.map (loopMapReg clonedDefs off c)) f (as.map (loopMapArg clonedDefs off c))

/-! ## Loop structure helpers and decidable preconditions -/

/-- Whether a list of `Nat`s is strictly increasing. -/
def isStrictlySorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictlySorted (b :: rest)

/-- Find the index of `target` in a `List Nat`. -/
def listIndexOf (xs : List Nat) (target : Nat) : Option Nat :=
  let rec go (i : Nat) : List Nat → Option Nat
    | [] => none
    | x :: rest => if x == target then some i else go (i + 1) rest
  go 0 xs

/-- Collect all virtual registers defined anywhere in a block list `lbls` of `F`. -/
def collectBlocksDefs (F : Func) (lbls : List Label) : Src.NatSet :=
  lbls.foldl (init := .leaf) fun acc b =>
    match F.blocks[b]? with
    | none => acc
    | some blk =>
        let acc := blk.params.foldl (fun s x => s.insert x) acc
        let acc := blk.body.foldl (fun s st => st.defs.foldl (fun a x => a.insert x) s) acc
        blk.term.defs.foldl (fun s x => s.insert x) acc

/-- Step an available-register set across a list of statements, checking that every used
register in `clonedDefs` is already in `av`. -/
def checkStmtsAvail (clonedDefs : Src.NatSet) (av : Src.NatSet) :
    List Stmt → Option Src.NatSet
  | [] => some av
  | s :: rest =>
      if s.uses.all (fun x => !clonedDefs.contains x || av.contains x) then
        checkStmtsAvail clonedDefs (s.defs.foldl (fun a x => a.insert x) av) rest
      else none

/-- Check that a witness `availMap : Array Src.NatSet` certifies that every use of a
register in `clonedDefs` inside `nodes ++ leafExits` is guaranteed defined within the
current loop iteration (making the simulation proof 100% independent of SSA). -/
def checkLoopAvail (F : Func) (h : Label) (nodes leafExits : List Label)
    (clonedDefs : Src.NatSet) (availMap : Array Src.NatSet) : Bool :=
  let nodeSet := Src.NatSet.ofList nodes
  let leafSet := Src.NatSet.ofList leafExits
  availMap.size == F.blocks.size &&
  (match F.blocks[h]?, availMap[h]? with
   | some hBlk, some avH => avH.toList.all fun (x, _) => hBlk.params.contains x
   | _, _ => false) &&
  (nodes ++ leafExits).all fun b =>
    match F.blocks[b]?, availMap[b]? with
    | some blk, some av0 =>
        match checkStmtsAvail clonedDefs av0 blk.body.toList with
        | none => false
        | some av1 =>
            blk.term.uses.all (fun x => !clonedDefs.contains x || av1.contains x) &&
            let av2 := blk.term.defs.foldl (fun a x => a.insert x) av1
            blk.term.edgeUses.all (fun x => !clonedDefs.contains x || av2.contains x) &&
            blk.term.edges.all fun e =>
              if (nodeSet.contains e.target && e.target != h) || leafSet.contains e.target then
                match F.blocks[e.target]?, availMap[e.target]? with
                | some tBlk, some avT =>
                    avT.toList.all fun (x, _) => av2.contains x || tBlk.params.contains x
                | _, _ => false
              else true
    | _, _ => false

/-- Untrusted helper to compute a valid `availMap` for `(nodes, leafExits)` in one forward pass. -/
def computeLoopAvail (F : Func) (h : Label) (nodes leafExits : List Label) : Array Src.NatSet :=
  let n := F.blocks.size
  let init : Array (Option Src.NatSet) := (Array.replicate n none).set! h
    (some (Src.NatSet.ofList ((F.blocks[h]?.map (·.params)).getD [])))
  let meetSet (a b : Src.NatSet) : Src.NatSet :=
    a.toList.foldl (init := .leaf) fun acc (x, _) => if b.contains x then acc.insert x else acc
  let addEdge (acc : Array (Option Src.NatSet)) (avSrc : Src.NatSet) (tgt : Label) :
      Array (Option Src.NatSet) :=
    if tgt < acc.size then
      let params := (F.blocks[tgt]?.map (·.params)).getD []
      let avIn := params.foldl (fun s x => s.insert x) avSrc
      match acc[tgt]! with
      | none => acc.set! tgt (some avIn)
      | some old => acc.set! tgt (some (meetSet old avIn))
    else acc
  let propagated := nodes.foldl (init := init) fun acc b =>
    match acc[b]?, F.blocks[b]? with
    | some (some av0), some blk =>
        let av1 := blk.body.foldl (init := av0) fun a s => s.defs.foldl (fun m x => m.insert x) a
        let av2 := blk.term.defs.foldl (fun m x => m.insert x) av1
        blk.term.edges.foldl (init := acc) fun a e =>
          if e.target == h then a else addEdge a av2 e.target
    | _, _ => acc
  let nodeSet := Src.NatSet.ofList nodes
  let outsideTargetsLeaf (b : Label) : Bool :=
    (List.range n).any fun u =>
      !nodeSet.contains u &&
      match F.blocks[u]? with
      | some blk => blk.term.edges.any fun e => e.target == b
      | none => false
  (List.range n).toArray.map fun b =>
    if leafExits.contains b && outsideTargetsLeaf b then
      Src.NatSet.ofList ((F.blocks[b]?.map (·.params)).getD [])
    else match propagated[b]? with
    | some (some s) => s
    | _ =>
        if leafExits.contains b then
          Src.NatSet.ofList ((F.blocks[b]?.map (·.params)).getD [])
        else .leaf

/-- Core decidable loop-cloning precondition shared by `unrollLoopSite` and `versionOddLoopSite`. -/
def loopCloneOk (F : Func) (h : Label) (nodes leafExits nonLeafExits : List Label)
    (off : VReg) (availMap : Array Src.NatSet) : Bool :=
  let n := F.blocks.size
  let maxNode := nodes.getLastD h
  let cut := maxNode + 1
  let nodeSet := Src.NatSet.ofList nodes
  let leafSet := Src.NatSet.ofList leafExits
  let nonLeafSet := Src.NatSet.ofList nonLeafExits
  let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
  0 < h &&
  !nodes.isEmpty &&
  nodes.head? == some h &&
  isStrictlySorted nodes &&
  isStrictlySorted leafExits &&
  isStrictlySorted nonLeafExits &&
  nodes.all (fun b => decide (b < n)) &&
  leafExits.all (fun b => decide (0 < b) && decide (b < n) && !nodeSet.contains b) &&
  nonLeafExits.all (fun b => decide (cut ≤ b) && decide (b < n) && !nodeSet.contains b && !leafSet.contains b) &&
  funcRegsLt F off &&
  -- Every leaf exit truly has no outgoing CFG edges
  leafExits.all (fun b => match F.blocks[b]? with | some blk => blk.term.edges.isEmpty | none => false) &&
  -- All edges from `nodes` are either back-edges to `h`, strictly forward inside `nodes`,
  -- to `leafExits`, or to `nonLeafExits`
  nodes.all (fun b =>
    match F.blocks[b]? with
    | none => false
    | some blk =>
        blk.term.edges.all fun e =>
          e.target == h ||
          (nodeSet.contains e.target && decide (b < e.target)) ||
          (leafSet.contains e.target && decide (b < e.target)) ||
          nonLeafSet.contains e.target) &&
  -- Outside blocks: only enter `nodes` at `h`, and non-leaf outside blocks never use `clonedDefs`
  (List.range n).all (fun u =>
    if nodeSet.contains u then true
    else match F.blocks[u]? with
    | none => false
    | some blk =>
        blk.term.edges.all (fun e =>
          (!nodeSet.contains e.target || e.target == h) &&
          (!leafSet.contains e.target ||
            match F.blocks[e.target]?, availMap[e.target]? with
            | some tBlk, some avT => avT.toList.all fun (x, _) => tBlk.params.contains x
            | _, _ => false)) &&
        (leafSet.contains u ||
          (blk.body.toList.all (fun s => s.uses.all fun x => !clonedDefs.contains x) &&
           blk.term.uses.all (fun x => !clonedDefs.contains x) &&
           blk.term.edgeUses.all (fun x => !clonedDefs.contains x)))) &&
  -- Available-register witness passes
  checkLoopAvail F h nodes leafExits clonedDefs availMap

/-! ## Helper: building trampoline blocks for non-leaf exits -/

/-- Build `nonLeafExits.length` 0-stmt trampoline blocks forwarding to `x + delta` using
disjoint fresh parameter registers starting at `trampRegBase`. -/
def buildTrampBlocks (F : Func) (nonLeafExits : List Label) (delta : Nat)
    (trampRegBase : VReg) (stride : Nat) : List Block :=
  nonLeafExits.zipIdx.map fun (x, idx) =>
    let nParams := (F.blocks[x]?.map (·.params.length)).getD 0
    let regStart := trampRegBase + idx * stride
    let ps := (List.range nParams).map (regStart + ·)
    { params := ps
      body := #[]
      term := .jump { target := x + delta, args := ps.map .v }
      cold := (F.blocks[x]?.map (·.cold)).getD false }

/-- Shift a `Term`'s arguments/defs for copy `c` and remap every outgoing edge via `remapEdge`. -/
def mapLoopTerm (clonedDefs : Src.NatSet) (off c : Nat) (remapTarget : Label → Label) : Term → Term
  | .jump e =>
      .jump { target := remapTarget e.target, args := e.args.map (loopMapArg clonedDefs off c) }
  | .br cond w a b t f =>
      .br cond w (loopMapArg clonedDefs off c a) (loopMapArg clonedDefs off c b)
        { target := remapTarget t.target, args := t.args.map (loopMapArg clonedDefs off c) }
        { target := remapTarget f.target, args := f.args.map (loopMapArg clonedDefs off c) }
  | .brOvf o x a b ok ovf =>
      .brOvf o (loopMapReg clonedDefs off c x) (loopMapArg clonedDefs off c a)
        (loopMapArg clonedDefs off c b)
        { target := remapTarget ok.target, args := ok.args.map (loopMapArg clonedDefs off c) }
        { target := remapTarget ovf.target, args := ovf.args.map (loopMapArg clonedDefs off c) }
  | .ret as => .ret (as.map (loopMapArg clonedDefs off c))
  | .tail f as => .tail f (as.map (loopMapArg clonedDefs off c))
  | .fail r => .fail r
  | .trap => .trap

/-! ## 1. `U`-way bounded loop unrolling (`unrollLoopSite`) -/

/-- Build the `U`-way unrolled function for validated loop `(h, nodes, leafExits, nonLeafExits)`.
Layout:
- `[0 .. maxNode]`: original prefix/copy-0 blocks (`nodes` back-edges redirected to copy 1;
  non-leaf exits redirected to copy-0 trampolines at `cut .. cut + T - 1`).
- `[cut .. cut + T - 1]`: copy-0 trampolines for `nonLeafExits`.
- For each `c ∈ {1, ..., U - 1}` (block stride `S = K + E + T`):
  - `K` cloned loop blocks (`nodes`),
  - `E` cloned leaf exit blocks (`leafExits`),
  - `T` trampolines for `nonLeafExits`.
- `[cut + delta .. n + delta - 1]`: shifted suffix blocks (original `cut .. n - 1`). -/
def buildUnrolledFunc (F : Func) (h : Label) (nodes leafExits nonLeafExits : List Label)
    (U : Nat) (off : VReg) : Func :=
  let maxNode := nodes.getLastD h
  let cut := maxNode + 1
  let K := nodes.length
  let E := leafExits.length
  let T := nonLeafExits.length
  let copyStride := K + E + T
  let delta := T + (U - 1) * copyStride
  let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
  let nodeSet := Src.NatSet.ofList nodes
  let copyNodeBase (c : Nat) : Label := cut + T + (c - 1) * copyStride
  let copyExitBase (c : Nat) : Label := copyNodeBase c + K
  let copyTrampBase (c : Nat) : Label :=
    if c == 0 then cut else copyNodeBase c + K + E
  let remapOrig (L : Label) : Label := if L < cut then L else L + delta
  let remapCopyTarget (c : Nat) (tgt : Label) : Label :=
    if tgt == h then
      if c + 1 < U then copyNodeBase (c + 1) else h
    else if nodeSet.contains tgt then
      if c == 0 then tgt
      else match listIndexOf nodes tgt with
      | some idx => copyNodeBase c + idx
      | none => tgt
    else
      match listIndexOf leafExits tgt with
      | some eidx => if c == 0 then remapOrig tgt else copyExitBase c + eidx
      | none =>
          match listIndexOf nonLeafExits tgt with
          | some tidx => copyTrampBase c + tidx
          | none => remapOrig tgt
  let prefixBlks : List Block :=
    (List.range cut).map fun b =>
      let blk := F.blocks[b]!
      if nodeSet.contains b then
        { blk with term := mapLoopTerm clonedDefs off 0 (remapCopyTarget 0) blk.term }
      else
        { blk with term := blk.term.setEdges (blk.term.edges.map fun e => { e with target := remapOrig e.target }) }
  let trampRegBase (c : Nat) : VReg := U * off + c * (T * off)
  let copy0Tramps : List Block := buildTrampBlocks F nonLeafExits delta (trampRegBase 0) off
  let copiesBlks : List Block :=
    (List.range (U - 1)).flatMap fun ci =>
      let c := ci + 1
      let cNodes : List Block := nodes.map fun b =>
        let blk := F.blocks[b]!
        { params := blk.params.map (loopMapReg clonedDefs off c)
          body := blk.body.map (loopMapStmt clonedDefs off c)
          term := mapLoopTerm clonedDefs off c (remapCopyTarget c) blk.term
          cold := blk.cold }
      let cExits : List Block := leafExits.map fun b =>
        let blk := F.blocks[b]!
        { params := blk.params.map (loopMapReg clonedDefs off c)
          body := blk.body.map (loopMapStmt clonedDefs off c)
          term := mapLoopTerm clonedDefs off c (fun l => l) blk.term
          cold := blk.cold }
      let cTramps : List Block := buildTrampBlocks F nonLeafExits delta (trampRegBase c) off
      cNodes ++ cExits ++ cTramps
  let suffixBlks : List Block :=
    (List.range (F.blocks.size - cut)).map fun d =>
      let blk := F.blocks[cut + d]!
      { blk with term := blk.term.setEdges (blk.term.edges.map fun e => { e with target := remapOrig e.target }) }
  { F with blocks := (prefixBlks ++ copy0Tramps ++ copiesBlks ++ suffixBlks).toArray }

/-- Collect `(nodes, leafExits, nonLeafExits)` for natural loop header `h` in `F`. -/
def classifyLoopExits (F : Func) (h : Label) :
    Option (List Label × List Label × List Label) :=
  let n := F.blocks.size
  if h == 0 || h ≥ n then none
  else
    let doms := F.dominators
    let preds := F.preds
    let backSrcs := (preds[h]!).filter fun b => Lir.Func.dominates doms h b
    if backSrcs.isEmpty then none
    else
      let nodeSet := naturalLoopNodes n preds h backSrcs
      let nodes := (List.range n).filter nodeSet.contains
      let maxNode := nodes.getLastD h
      let cut := maxNode + 1
      let exitTargets : List Label :=
        ((nodes.flatMap fun b =>
            match F.blocks[b]? with
            | some blk => blk.term.edges.map (·.target)
            | none => []).filter fun t => !nodeSet.contains t).eraseDups.mergeSort (· ≤ ·)
      let leafExits := exitTargets.filter fun t =>
        match F.blocks[t]? with
        | some blk => blk.term.edges.isEmpty
        | none => false
      let nonLeafExits := exitTargets.filter fun t =>
        match F.blocks[t]? with
        | some blk => !blk.term.edges.isEmpty && decide (cut ≤ t)
        | none => false
      some (nodes, leafExits, nonLeafExits)

/-- Unroll the natural loop at `(fi, h)` by factor `U ≥ 2` if all soundness preconditions hold. -/
def unrollLoopSite (p : Program) (fi : FunId) (h : Label) (U : Nat) : Option Program :=
  if U < 2 then none
  else match p.funcs[fi]? with
  | none => none
  | some F =>
      match classifyLoopExits F h with
      | none => none
      | some (nodes, leafExits, nonLeafExits) =>
          let off := nextFreshVReg F
          let availMap := computeLoopAvail F h nodes leafExits
          if loopCloneOk F h nodes leafExits nonLeafExits off availMap then
            let F' := buildUnrolledFunc F h nodes leafExits nonLeafExits U off
            some { p with funcs := p.funcs.set! fi F' }
          else none

/-- Checked single-site loop unrolling preserving `WellFormed`. -/
def unrollLoopSiteChecked (p : Program) (fi : FunId) (h : Label) (U : Nat) : Program × Bool :=
  match unrollLoopSite p fi h U with
  | none => (p, false)
  | some q => if !p.wellFormed || q.wellFormed then (q, true) else (p, false)

/-! ## 2. Odd-fixnum loop versioning (`versionOddLoopSite`) -/

/-- Build a pure left-folded bitwise-AND chain over `regs` using fresh registers starting at
`nextReg`, returning `(stmts, finalTestReg)`. -/
def buildDispAndChainAux (accReg nextReg : VReg) : List VReg → List Stmt × VReg
  | [] => ([], accReg)
  | r :: rest =>
      let (ss, finalReg) := buildDispAndChainAux nextReg (nextReg + 1) rest
      (.assign nextReg (.bin .and .w64 (.v accReg) (.v r)) :: ss, finalReg)

/-- Build the dispatch-block bitwise-AND body and final test register for a non-empty list `regs`. -/
def buildDispAndChain (regs : List VReg) (andBase : VReg) : List Stmt × VReg :=
  match regs with
  | [] => ([], andBase)
  | [r] => ([], r)
  | r0 :: rest => buildDispAndChainAux r0 andBase rest

/-- Additional decidable check for `versionOddLoopSite`:
- at least one tested register in `testParamIdxs` or `outerTestRegs`,
- every `idx ∈ testParamIdxs` satisfies `idx < h.params.length`,
- every `r ∈ outerTestRegs` is a function parameter `< off` not redefined in `clonedDefs`,
- every outside predecessor `u ∉ nodes` of `h` satisfies `u < h` or `cut ≤ u` (so redirecting
  `u → h` to `disp = cut` preserves the forward/backward clock direction of `u → disp`!). -/
def versionOddLoopOk (F : Func) (h : Label) (nodes leafExits nonLeafExits : List Label)
    (testParamIdxs : List Nat) (outerTestRegs : List VReg) (off : VReg)
    (availMap : Array Src.NatSet) : Bool :=
  let maxNode := nodes.getLastD h
  let cut := maxNode + 1
  let nodeSet := Src.NatSet.ofList nodes
  let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
  loopCloneOk F h nodes leafExits nonLeafExits off availMap &&
  !(testParamIdxs.isEmpty && outerTestRegs.isEmpty) &&
  (match F.blocks[h]? with
   | some hBlk => testParamIdxs.all fun i => decide (i < hBlk.params.length)
   | none => false) &&
  outerTestRegs.all (fun r => F.params.contains r && decide (r < off) && !clonedDefs.contains r) &&
  (List.range F.blocks.size).all fun u =>
    if nodeSet.contains u then true
    else match F.blocks[u]? with
    | none => false
    | some blk =>
        blk.term.edges.all fun e =>
          e.target != h || decide (u < h) || decide (cut ≤ u)

/-- Build the odd-fixnum versioned function for loop `(h, nodes)`.
Layout:
- `[0 .. maxNode]`: original prefix & slow loop (outside edges `u → h` redirected to `disp = cut`;
  slow loop non-leaf exits redirected to `slowTramps`).
- `cut`: `disp` (computes bitwise-AND of all `outerTestRegs` and `dispParams[testParamIdxs]`,
  then `br .tnz testReg, 1 -> fastHop, slowHop`).
- `cut + 1`: `slowHop` (`jump h(dispParams)`).
- `cut + 2`: `fastHop` (`jump fastBase(dispParams)`).
- `cut + 3 .. cut + 3 + T - 1`: `slowTramps`.
- `fastBase = cut + 3 + T`: `K` fast loop blocks (whose back-edges to `h` re-enter `disp = cut`
  so an overflowed BigNat return automatically deoptimizes to the slow loop while keeping every
  fast-header variable provably odd!) + `E` fast leaf exits + `T` fast trampolines.
- `[cut + delta .. n + delta - 1]`: shifted suffix blocks. -/
def buildVersionedOddFunc (F : Func) (h : Label) (nodes leafExits nonLeafExits : List Label)
    (testParamIdxs : List Nat) (outerTestRegs : List VReg) (off : VReg) : Func :=
  let maxNode := nodes.getLastD h
  let cut := maxNode + 1
  let K := nodes.length
  let E := leafExits.length
  let T := nonLeafExits.length
  let dispLbl := cut
  let slowHopLbl := cut + 1
  let fastHopLbl := cut + 2
  let slowTrampBase := cut + 3
  let fastNodeBase := cut + 3 + T
  let fastExitBase := fastNodeBase + K
  let fastTrampBase := fastExitBase + E
  let delta := 3 + T + K + E + T
  let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
  let nodeSet := Src.NatSet.ofList nodes
  let hBlk := F.blocks[h]!
  let dispParams := (List.range hBlk.params.length).map (2 * off + ·)
  let andBase := max (2 * off + hBlk.params.length) (3 * off + 2 * T * off)
  let testRegs := outerTestRegs ++ testParamIdxs.map (fun i => dispParams[i]?.getD (2 * off))
  let (dispBody, testReg) := buildDispAndChain testRegs andBase
  let dispBlk : Block :=
    { params := dispParams
      body := dispBody.toArray
      term := .br .tnz .w64 (.v testReg) (.imm 1)
        { target := fastHopLbl, args := [] } { target := slowHopLbl, args := [] }
      cold := hBlk.cold }
  let slowHopBlk : Block :=
    { params := []
      body := #[]
      term := .jump { target := h, args := dispParams.map .v }
      cold := true }
  let fastHopBlk : Block :=
    { params := []
      body := #[]
      term := .jump { target := fastNodeBase, args := dispParams.map .v }
      cold := hBlk.cold }
  let remapOrig (L : Label) : Label := if L < cut then L else L + delta
  let remapOutside (tgt : Label) : Label :=
    if tgt == h then dispLbl else remapOrig tgt
  let remapSlowTarget (tgt : Label) : Label :=
    if tgt == h || nodeSet.contains tgt then tgt
    else match listIndexOf nonLeafExits tgt with
    | some tidx => slowTrampBase + tidx
    | none => remapOrig tgt
  let remapFastTarget (tgt : Label) : Label :=
    if tgt == h then dispLbl
    else if nodeSet.contains tgt then
      match listIndexOf nodes tgt with
      | some idx => fastNodeBase + idx
      | none => tgt
    else match listIndexOf leafExits tgt with
    | some eidx => fastExitBase + eidx
    | none =>
        match listIndexOf nonLeafExits tgt with
        | some tidx => fastTrampBase + tidx
        | none => remapOrig tgt
  let prefixBlks : List Block :=
    (List.range cut).map fun b =>
      let blk := F.blocks[b]!
      if nodeSet.contains b then
        { blk with term := mapLoopTerm clonedDefs off 0 remapSlowTarget blk.term, cold := true }
      else
        { blk with term := blk.term.setEdges (blk.term.edges.map fun e => { e with target := remapOutside e.target }) }
  let slowTramps := buildTrampBlocks F nonLeafExits delta (3 * off) off
  let fastTramps := buildTrampBlocks F nonLeafExits delta (3 * off + T * off) off
  let fastNodes : List Block := nodes.map fun b =>
    let blk := F.blocks[b]!
    { params := blk.params.map (loopMapReg clonedDefs off 1)
      body := blk.body.map (loopMapStmt clonedDefs off 1)
      term := mapLoopTerm clonedDefs off 1 remapFastTarget blk.term
      cold := blk.cold }
  let fastExits : List Block := leafExits.map fun b =>
    let blk := F.blocks[b]!
    { params := blk.params.map (loopMapReg clonedDefs off 1)
      body := blk.body.map (loopMapStmt clonedDefs off 1)
      term := mapLoopTerm clonedDefs off 1 (fun l => l) blk.term
      cold := blk.cold }
  let suffixBlks : List Block :=
    (List.range (F.blocks.size - cut)).map fun d =>
      let blk := F.blocks[cut + d]!
      { blk with term := blk.term.setEdges (blk.term.edges.map fun e => { e with target := remapOutside e.target }) }
  { F with
    blocks := (prefixBlks ++ [dispBlk, slowHopBlk, fastHopBlk] ++ slowTramps ++
      fastNodes ++ fastExits ++ fastTramps ++ suffixBlks).toArray }

/-- Specialize natural loop `(fi, h)` on `outerTestRegs` and `h.params[testParamIdxs]` being odd. -/
def versionOddLoopSite (p : Program) (fi : FunId) (h : Label)
    (testParamIdxs : List Nat) (outerTestRegs : List VReg := []) : Option Program :=
  match p.funcs[fi]? with
  | none => none
  | some F =>
      match classifyLoopExits F h with
      | none => none
      | some (nodes, leafExits, nonLeafExits) =>
          let off := nextFreshVReg F
          let availMap := computeLoopAvail F h nodes leafExits
          if versionOddLoopOk F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off availMap then
            let F' := buildVersionedOddFunc F h nodes leafExits nonLeafExits testParamIdxs outerTestRegs off
            some { p with funcs := p.funcs.set! fi F' }
          else none

/-- Checked single-site odd-loop versioning preserving `WellFormed`. -/
def versionOddLoopSiteChecked (p : Program) (fi : FunId) (h : Label)
    (testParamIdxs : List Nat) (outerTestRegs : List VReg := []) : Program × Bool :=
  match versionOddLoopSite p fi h testParamIdxs outerTestRegs with
  | none => (p, false)
  | some q => if !p.wellFormed || q.wellFormed then (q, true) else (p, false)

/-! ## Heuristic site pickers -/

/-- Whether a loop body contains a tag test (`br .tz/.tnz _ 1`) on parameter `p` (or `p &&& _` / `_ &&& p`),
indicating a `--bignat` scalar loop that benefits from odd-fixnum versioning! -/
private def loopTestsTagOnParam (F : Func) (nodes : List Label) (p : VReg) : Bool :=
  let andOfP : Src.NatSet := nodes.foldl (init := Src.NatSet.ofList [p]) fun acc b =>
    match F.blocks[b]? with
    | none => acc
    | some blk =>
        blk.body.foldl (init := acc) fun s st =>
          match st with
          | .assign x (.bin .and .w64 (.v a) (.v b')) =>
              if s.contains a || s.contains b' then s.insert x else s
          | _ => s
  nodes.any fun b =>
    match F.blocks[b]? with
    | none => false
    | some blk =>
        match blk.term with
        | .br .tz .w64 (.v r) (.imm 1) _ _ | .br .tnz .w64 (.v r) (.imm 1) _ _
        | .br .tz .w64 (.imm 1) (.v r) _ _ | .br .tnz .w64 (.imm 1) (.v r) _ _ =>
            andOfP.contains r
        | _ => false

/-- Find an eligible natural loop `(h, testParamIdxs, outerTestRegs)` in `F` for odd-fixnum versioning.
Tests ALL header parameters and function parameters involved in `--bignat` tag checks inside the loop! -/
def findVersionOddLoopSite (F : Func) : Option (Label × List Nat × List VReg) :=
  let n := F.blocks.size
  if n ≤ 1 || n > 80 then none
  else
    -- Prefer innermost hot loops first (or all loops without stores)
    (List.range n).reverse.findSome? fun h =>
      match classifyLoopExits F h with
      | none => none
      | some (nodes, leafExits, nonLeafExits) =>
          let loopStmts := nodes.foldl (fun acc b => acc + (F.blocks[b]?.map (·.body.size)).getD 0) 0
          let hasStore := nodes.any fun b =>
            match F.blocks[b]? with
            | some blk => blk.body.any fun | .store .. => true | _ => false
            | none => false
          if nodes.length > 24 || loopStmts > 64 || hasStore then none
          else
            let off := nextFreshVReg F
            let availMap := computeLoopAvail F h nodes leafExits
            let clonedDefs := collectBlocksDefs F (nodes ++ leafExits)
            match F.blocks[h]? with
            | none => none
            | some hBlk =>
                if hBlk.cold then none
                else
                  let paramIdxs := hBlk.params.zipIdx.filterMap fun (p, idx) =>
                    if loopTestsTagOnParam F nodes p then some idx else none
                  let outerRegs := (F.params.filter fun r =>
                    !clonedDefs.contains r && loopTestsTagOnParam F nodes r).eraseDups
                  if !(paramIdxs.isEmpty && outerRegs.isEmpty) &&
                     versionOddLoopOk F h nodes leafExits nonLeafExits paramIdxs outerRegs off availMap then
                    some (h, paramIdxs, outerRegs)
                  else none

/-- Find an eligible tight scalar natural loop `(h, U)` in `F` for bounded `U`-way unrolling. -/
def findUnrollLoopSite (F : Func) : Option (Label × Nat) :=
  let n := F.blocks.size
  if n ≤ 1 || n > 100 then none
  else
    -- Prefer innermost hot loops (descending header index)
    (List.range n).reverse.findSome? fun h =>
      match classifyLoopExits F h with
      | none => none
      | some (nodes, leafExits, nonLeafExits) =>
          match F.blocks[h]? with
          | none => none
          | some hBlk =>
              if hBlk.cold then none
              else
                let loopStmts := nodes.foldl (fun acc b => acc + (F.blocks[b]?.map (·.body.size)).getD 0) 0
                let hasCallOrStore := nodes.any fun b =>
                  match F.blocks[b]? with
                  | some blk => blk.body.any fun | .call .. | .store .. => true | _ => false
                  | none => false
                if hasCallOrStore || nodes.length > 6 || loopStmts > 18 then none
                else
                  let U := if nodes.length ≤ 5 && loopStmts ≤ 12 then 4 else 2
                  let extra := nonLeafExits.length + (U - 1) * (nodes.length + leafExits.length + nonLeafExits.length)
                  if n + extra > 120 then none
                  else
                    let off := nextFreshVReg F
                    let availMap := computeLoopAvail F h nodes leafExits
                    if loopCloneOk F h nodes leafExits nonLeafExits off availMap then
                      some (h, U)
                    else none

end IxCC.Lir.Opt
