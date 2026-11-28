import IxCC.Lir.Opt.Sym
import IxCC.Lir.Graph
import IxCC.Lir.SplitEdges
import IxCC.Src.NatMap

/-!
# Natural-loop LICM and invariant check hoisting (untrusted optimizer)

Detects natural loops on a `Lir.Func` CFG using dominator sets (`Lir.Graph`),
and performs four loop optimizations while preserving `WellFormed` (SSA
dominance, no critical edges, exact back-edge charges):

1. **Loop-invariant block parameter substitution**: when a loop header parameter
   `pᵢ` receives itself on every back-edge and the same dominating value `a₀` on
   every outside entry edge, replaces loop-body uses (and back-edge passes) of
   `pᵢ` with `a₀`. This unlocks LICM for expressions like `shr v0 1` in
   `prime-count`.
2. **Preheader identification & insertion**: uses an existing dedicated single
   preheader when present, or inserts a new preheader block right before the
   loop header for multi-entry loops (preserving exact clock charges).
3. **Pure loop-invariant code motion (LICM)**: iteratively hoists pure, total
   (non-trapping, non-memory) loop-invariant statements (`assign` and pure
   `limb` ops) out of loop bodies into the preheader.
4. **Invariant fail-guard hoisting**: hoists loop-invariant `.fail r` guard
   branches that execute unconditionally at loop entry into the preheader
   (splitting the ok-edge via a trampoline hop so no critical edge is created)
   and folds the redundant check inside the loop to `.jump`.

This pass is **untrusted**; its output is checked by `Lir.Opt.check`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Label FunId Width Ext Base Addr Arg Cond BinOp Ovf LimbOp
  Rhs Stmt Edge Term Block Func)

/-! ## Helpers -/

/-- Fresh register strictly above every register appearing in `F`. -/
def nextFreshVReg (F : Func) : VReg :=
  let maxList (xs : List VReg) (acc : VReg) : VReg := xs.foldl max acc
  let m0 := maxList F.params 0
  let m1 := F.blocks.foldl (init := m0) fun acc b =>
    let acc := maxList b.params acc
    let acc := b.body.foldl (init := acc) fun a s => maxList s.uses (maxList s.defs a)
    maxList b.term.edgeUses (maxList b.term.defs (maxList b.term.uses acc))
  m1 + 1

/-- Whether a statement is pure and total (safe to hoist speculatively before a loop). -/
def isHoistableStmt : Stmt → Bool
  | .assign _ r =>
      match r with
      | .arg _ | .addr _ | .select .. | .test .. => true
      | .bin o w _ b =>
          binOpIsTotal o || match b with | .imm k => w.truncate k != 0 | _ => false
      | .bsr64 (.imm k) => k != 0
      | .bsr64 _ | .load .. => false
  | .limb _ _ op =>
      match op with
      | .mulWide64 .. | .addCarry64 .. | .subBorrow64 .. => true
      | .divWide64 .. => false
  | .store .. | .call .. => false

/-- Substitute register occurrences according to `env : Src.NatMap Arg`. -/
def substArg (env : Src.NatMap Arg) : Arg → Arg
  | .v x => env.getD x (.v x)
  | .imm w => .imm w

def substAddr (env : Src.NatMap Arg) (m : Addr) : Addr :=
  let base := match m.base with
    | some (.v x) =>
        match env.get? x with
        | some (.v y) => some (.v y)
        | _ => some (.v x)
    | b => b
  let index := match m.index with
    | some (x, s) =>
        match env.get? x with
        | some (.v y) => some (y, s)
        | _ => some (x, s)
    | none => none
  { m with base, index }

def substRhs (env : Src.NatMap Arg) : Rhs → Rhs
  | .arg a => .arg (substArg env a)
  | .bin o w a b => .bin o w (substArg env a) (substArg env b)
  | .load w e m => .load w e (substAddr env m)
  | .addr m => .addr (substAddr env m)
  | .select c w a b t f =>
      .select c w (substArg env a) (substArg env b) (substArg env t) (substArg env f)
  | .test c w a b => .test c w (substArg env a) (substArg env b)
  | .bsr64 a => .bsr64 (substArg env a)

def substLimb (env : Src.NatMap Arg) : LimbOp → LimbOp
  | .mulWide64 a b => .mulWide64 (substArg env a) (substArg env b)
  | .divWide64 hi lo d => .divWide64 (substArg env hi) (substArg env lo) (substArg env d)
  | .addCarry64 a b c => .addCarry64 (substArg env a) (substArg env b) (substArg env c)
  | .subBorrow64 a b c => .subBorrow64 (substArg env a) (substArg env b) (substArg env c)

def substStmt (env : Src.NatMap Arg) : Stmt → Stmt
  | .assign x r => .assign x (substRhs env r)
  | .limb r1 r2 op => .limb r1 r2 (substLimb env op)
  | .store w m a => .store w (substAddr env m) (substArg env a)
  | .call rs f as => .call rs f (as.map (substArg env))

def substEdge (env : Src.NatMap Arg) (e : Edge) : Edge :=
  { e with args := e.args.map (substArg env) }

def substTerm (env : Src.NatMap Arg) : Term → Term
  | .jump e => .jump (substEdge env e)
  | .br c w a b t f => .br c w (substArg env a) (substArg env b) (substEdge env t) (substEdge env f)
  | .brOvf o x a b ok ovf => .brOvf o x (substArg env a) (substArg env b) (substEdge env ok) (substEdge env ovf)
  | .ret as => .ret (as.map (substArg env))
  | .tail f as => .tail f (as.map (substArg env))
  | .fail r => .fail r
  | .trap => .trap

def substBlock (env : Src.NatMap Arg) (b : Block) : Block :=
  { b with body := b.body.map (substStmt env), term := substTerm env b.term }

/-- Map each defined register in `F` to its defining block label. -/
def defBlockMap (F : Func) : Src.NatMap Label :=
  let m0 := F.params.foldl (fun m x => m.insert x 0) Src.NatMap.empty
  (List.range F.blocks.size).foldl (init := m0) fun m b =>
    match F.blocks[b]? with
    | none => m
    | some blk =>
        let m := blk.params.foldl (fun m x => m.insert x b) m
        let m := blk.body.foldl (fun m s => s.defs.foldl (fun m x => m.insert x b) m) m
        blk.term.defs.foldl (fun m x => m.insert x b) m

/-- Natural loop nodes for header `h` given back-edge sources `backSrcs` and predecessor array `preds`. -/
def naturalLoopNodes (n : Nat) (preds : Array (List Label)) (h : Label) (backSrcs : List Label) :
    Src.NatSet :=
  let rec bfs : Nat → List Label → Src.NatSet → Src.NatSet
    | 0, _, seen => seen
    | _, [], seen => seen
    | fuel + 1, b :: work, seen =>
        let ps := (preds[b]?.getD []).filter fun p => !seen.contains p
        let seen' := ps.foldl (fun s p => s.insert p) seen
        bfs fuel (ps ++ work) seen'
  let init0 : Src.NatSet := Src.NatSet.ofList [h]
  let start := backSrcs.filter fun b => b != h
  let init : Src.NatSet := start.foldl (fun s b => Src.NatSet.insert s b) init0
  bfs (n * n + 2) start init

/-- Shift all edge targets `≥ cut` up by `delta`. -/
def shiftEdgeTargets (cut delta : Nat) (e : Edge) : Edge :=
  if e.target ≥ cut then { e with target := e.target + delta } else e

def shiftTermTargets (cut delta : Nat) (t : Term) : Term :=
  t.setEdges (t.edges.map (shiftEdgeTargets cut delta))

/-- Insert a dedicated preheader block right before loop header `h` (at label `h`),
redirecting all outside edges `u → h` (with `u ∉ loopNodes`) to `ph = h` while back-edges
from `loopNodes` go to `h + 1`. -/
def insertPreheader (F : Func) (h : Label) (loopNodes : Src.NatSet) : Func × Label :=
  match F.blocks[h]? with
  | none => (F, h)
  | some hdr =>
      let fresh0 := nextFreshVReg F
      let phParams := (List.range hdr.params.length).map (fresh0 + ·)
      let phBlk : Block :=
        { params := phParams
          body := #[]
          term := .jump { target := h + 1, args := phParams.map .v }
          cold := hdr.cold }
      let n := F.blocks.size
      let rewriteBlock (b : Label) (blk : Block) : Block :=
        let inLoop := loopNodes.contains b
        let newEdges := blk.term.edges.map fun e =>
          if e.target == h then
            if inLoop then { e with target := h + 1 }
            else { e with target := h } -- points to preheader `ph`!
          else shiftEdgeTargets h 1 e
        { blk with term := blk.term.setEdges newEdges }
      let before := (List.range h).filterMap fun b => (F.blocks[b]?).map (rewriteBlock b)
      let after := (List.range (n - h)).filterMap fun d =>
        let b := h + d
        (F.blocks[b]?).map (rewriteBlock b)
      ({ F with blocks := (before ++ [phBlk] ++ after).toArray }, h)

/-- Detect whether edge `e` goes with no args to an immediate `.fail r` block and return `r`. -/
def failEdgeResource? (F : Func) (e : Edge) : Option Sem.Resource :=
  if !e.args.isEmpty then none
  else match F.blocks[e.target]? with
  | some b =>
      if b.params.isEmpty && b.body.isEmpty then
        match b.term with | .fail r => some r | _ => none
      else none
  | none => none

/-- Find unconditional entry blocks of loop `h` (starting from `h`, following only
single-succ non-back forward edges inside `loopNodes` with no stores/calls). -/
def unconditionalLoopBlocks (F : Func) (loopNodes : Src.NatSet) (h : Label) : List Label :=
  let rec go : Nat → Label → Src.NatSet → List Label → List Label
    | 0, _, _, acc => acc.reverse
    | fuel + 1, b, seen, acc =>
        match F.blocks[b]? with
        | none => acc.reverse
        | some blk =>
            let acc' := b :: acc
            let hasEffect := blk.body.any fun | .store .. | .call .. => true | _ => false
            if hasEffect then acc'.reverse
            else match blk.term with
            | .jump e =>
                if e.target > b && loopNodes.contains e.target && !seen.contains e.target then
                  go fuel e.target (seen.insert e.target) acc'
                else acc'.reverse
            | .br _ _ _ _ t f =>
                -- Can continue past an immediate fail-guard!
                if (failEdgeResource? F f).isSome && t.target > b &&
                   loopNodes.contains t.target && !seen.contains t.target then
                  go fuel t.target (seen.insert t.target) acc'
                else if (failEdgeResource? F t).isSome && f.target > b &&
                   loopNodes.contains f.target && !seen.contains f.target then
                  go fuel f.target (seen.insert f.target) acc'
                else acc'.reverse
            | _ => acc'.reverse
  go (F.blocks.size + 1) h (Src.NatSet.ofList [h]) []

/-- Optimize one natural loop with header `h` (recomputing dominators cleanly).
Returns the updated function and a label-remapping function from old labels to new labels. -/
def optimizeLoop (F : Func) (h : Label) : Func × (Label → Label) :=
  let n := F.blocks.size
  if h == 0 || h ≥ n then (F, id)
  else
    let doms := F.dominators
    let preds := F.preds
    let backSrcs := (preds[h]!).filter fun b => Lir.Func.dominates doms h b
    if backSrcs.isEmpty then (F, id)
    else
      let loopNodes := naturalLoopNodes n preds h backSrcs
      let outsidePreds := (preds[h]!).filter fun p => !loopNodes.contains p
      if outsidePreds.isEmpty then (F, id)
      else
        -- Step 1: Loop-invariant block parameter substitution
        let hdr := F.blocks[h]!
        let defMap := defBlockMap F
        let domStrictH (a : Arg) : Bool :=
          match a with
          | .imm _ => true
          | .v x =>
              match defMap.get? x with
              | some db => db != h && Lir.Func.dominates doms db h
              | none => false
        let invSub : Src.NatMap Arg :=
          hdr.params.zipIdx.foldl (init := Src.NatMap.empty) fun sub (p, idx) =>
            -- Check all back-edges pass `.v p` at position `idx`
            let backOk := backSrcs.all fun b =>
              (F.blocks[b]!.term.edges.filter (·.target == h)).all fun e =>
                e.args[idx]? == some (.v p)
            if !backOk then sub
            else
              -- Check all outside edges pass the exact same dominating arg `a0`
              let outArgs := outsidePreds.flatMap fun u =>
                (F.blocks[u]!.term.edges.filter (·.target == h)).filterMap fun e => e.args[idx]?
              match outArgs with
              | [] => sub
              | a0 :: rest =>
                  if domStrictH a0 && rest.all (· == a0) then sub.insert p a0 else sub
        let F1 : Func :=
          if invSub.toList.isEmpty then F
          else
            let newBlocks := (List.range n).toArray.map fun b =>
              let blk := F.blocks[b]!
              if loopNodes.contains b then substBlock invSub blk else blk
            { F with blocks := newBlocks }
        -- Step 2: Check whether there is anything hoistable BEFORE inserting a new preheader
        let doms1 := F1.dominators
        let defMap1 := defBlockMap F1
        let domStrictH1 (x : VReg) : Bool :=
          match defMap1.get? x with
          | some db => db != h && Lir.Func.dominates doms1 db h
          | none => false
        let anyHoistable : Bool :=
          (loopNodes.toList.map Prod.fst).any fun b =>
            match F1.blocks[b]? with
            | none => false
            | some blk =>
                (blk.body.any fun s => isHoistableStmt s && s.uses.all domStrictH1) ||
                (match blk.term with
                 | .br _ _ a b' t f =>
                     ((failEdgeResource? F1 t).isSome || (failEdgeResource? F1 f).isSome) &&
                     (a.uses ++ b'.uses).all domStrictH1
                 | _ => false)
        if !anyHoistable then (F1, id)
        else
          -- Step 3: Locate existing dedicated preheader, or insert one for multi-entry loops
          let uniqueOutside := outsidePreds.eraseDups
          let dedicatedPh? : Option Label :=
            match uniqueOutside with
            | [ph] =>
                match F1.blocks[ph]? with
                | some phBlk =>
                    match phBlk.term with
                    | .jump e => if e.target == h then some ph else none
                    | _ => none
                | none => none
            | _ => none
          let (F2, ph, h2, loopNodes2, remap1) :=
            match dedicatedPh? with
            | some ph => (F1, ph, h, loopNodes, (id : Label → Label))
            | none =>
                let (Fins, phNew) := insertPreheader F1 h loopNodes
                let shiftedLoop := Src.NatSet.ofList ((loopNodes.toList.map Prod.fst).map fun b => if b ≥ h then b + 1 else b)
                (Fins, phNew, h + 1, shiftedLoop, fun l => if l ≥ h then l + 1 else l)
          -- Step 4: Iteratively hoist pure total loop-invariant statements into `ph`
          let doms2 := F2.dominators
          let defMap2 := defBlockMap F2
          let initHoisted : Src.NatSet :=
            Src.NatSet.ofList <| defMap2.toList.filterMap fun (x, db) =>
              if Lir.Func.dominates doms2 db ph then some x else none
          let loopOrder := F2.rpo.toList.filter loopNodes2.contains
          let hoistRound (cur : Func) (avail : Src.NatSet) : Func × Src.NatSet × Bool :=
            loopOrder.foldl (init := (cur, avail, false)) fun (fAcc, avAcc, chAcc) b =>
              match fAcc.blocks[b]? with
              | none => (fAcc, avAcc, chAcc)
              | some blk =>
                  let (kept, moved, av') := blk.body.foldl
                    (init := (#[], #[], avAcc)) fun (k, m, av) s =>
                      if isHoistableStmt s && s.uses.all av.contains then
                        let av1 := s.defs.foldl (fun a x => a.insert x) av
                        (k, m.push s, av1)
                      else (k.push s, m, av)
                  if moved.isEmpty then (fAcc, avAcc, chAcc)
                  else
                    let bs1 := fAcc.blocks.set! b { blk with body := kept }
                    let phBlk := bs1[ph]!
                    let bs2 := bs1.set! ph { phBlk with body := phBlk.body ++ moved }
                    ({ fAcc with blocks := bs2 }, av', true)
          let rec hoistFix : Nat → Func → Src.NatSet → Func × Src.NatSet
            | 0, cur, av => (cur, av)
            | fuel + 1, cur, av =>
                let (cur', av', ch) := hoistRound cur av
                if !ch then (cur', av') else hoistFix fuel cur' av'
          let (F3, avail3) := hoistFix 8 F2 initHoisted
          -- Step 5: Hoist invariant unconditional `.fail r` checks into `ph`
          -- (splitting `ph → h2` with a forward trampoline `hop` right after `ph` to avoid critical edges!)
          let unconds := unconditionalLoopBlocks F3 loopNodes2 h2
          let hoistableGuard? : Option (Label × Cond × Width × Arg × Arg × Edge × Sem.Resource × Bool) :=
            unconds.findSome? fun b =>
              match F3.blocks[b]? with
              | none => none
              | some blk =>
                  match blk.term with
                  | .br c w a b' t f =>
                      if (a.uses ++ b'.uses).all avail3.contains then
                        match failEdgeResource? F3 f with
                        | some r => some (b, c, w, a, b', t, r, false)
                        | none =>
                            match failEdgeResource? F3 t with
                            | some r => some (b, c, w, a, b', f, r, true)
                            | none => none
                      else none
                  | _ => none
          match hoistableGuard?, F3.blocks[ph]? with
          | some (gb, c, w, a, b', okEdge, res, failOnTrue), some phBlk =>
              match phBlk.term with
              | .jump eToH =>
                  -- Insert `hop` at index `ph + 1` (shifting labels `≥ ph + 1` up by 1),
                  -- and append `failBlk` at the end (no critical edge!).
                  let cut := ph + 1
                  let n3 := F3.blocks.size
                  let failIdx := n3 + 1
                  let hopBlk : Block :=
                    { params := []
                      body := #[]
                      term := .jump (shiftEdgeTargets cut 1 eToH)
                      cold := phBlk.cold }
                  let failBlk : Block := { params := [], body := #[], term := .fail res, cold := true }
                  let newPhTerm : Term :=
                    if failOnTrue then
                      .br c w a b' { target := failIdx, args := [] } { target := cut, args := [] }
                    else
                      .br c w a b' { target := cut, args := [] } { target := failIdx, args := [] }
                  let rewriteBlk (idx : Label) (blk : Block) : Block :=
                    if idx == ph then { blk with term := newPhTerm }
                    else if idx == gb then { blk with term := .jump (shiftEdgeTargets cut 1 okEdge) }
                    else { blk with term := shiftTermTargets cut 1 blk.term }
                  let before := (List.range cut).filterMap fun i => (F3.blocks[i]?).map (rewriteBlk i)
                  let after := (List.range (n3 - cut)).filterMap fun d =>
                    let i := cut + d
                    (F3.blocks[i]?).map (rewriteBlk i)
                  let remap2 (l : Label) : Label :=
                    let l' := remap1 l
                    if l' ≥ cut then l' + 1 else l'
                  ({ F3 with blocks := (before ++ [hopBlk] ++ after ++ [failBlk]).toArray }, remap2)
              | _ => (F3, remap1)
          | _, _ => (F3, remap1)

/-- Run LICM across all natural loops of `F` (innermost first, by descending header index). -/
def licmFunc (F : Func) : Func :=
  let n := F.blocks.size
  if n ≤ 1 then F
  else
    let doms := F.dominators
    let preds := F.preds
    let headers := ((List.range n).filter fun h =>
      h > 0 && (preds[h]!).any fun b => Lir.Func.dominates doms h b).reverse
    -- Process one header at a time, remapping remaining header labels cleanly
    let rec go : Nat → List Label → Func → Func
      | 0, _, cur => cur
      | _, [], cur => cur
      | fuel + 1, h :: rest, cur =>
          let (cur', remap) := optimizeLoop cur h
          go fuel (rest.map remap) cur'
    go (headers.length + 1) headers F

end IxCC.Lir.Opt
