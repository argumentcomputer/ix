import IxCC.Xv.Alloc.State

/-!
# The all-slots fallback

`Alloc.allSlots` (05 §5) keeps every virtual register in its own home cell
(a frame slot; an incoming cell for a stack parameter) at every
instruction boundary. Before an instruction, the registers it reads in
registers (`reg`, `fixed`, ties, a `move`'s source) are loaded from their
homes; `any` operands name the home directly; register definitions are
stored to their homes before the next instruction. A terminator's
definitions (a `brOvf` result) stay in their register to the successor's
head, which stores them. Edges bind parameters by moving arguments home to
home through a scratch register (`ParMove.resolve`).

It is the allocator of last resort: when linear scan fails or the validator
rejects its output, the driver allocates the function this way. It is still
checked (until `Alloc.allSlots_valid` is proved, M2.6); a rejection is a
compile error, never wrong code. Its only inputs are liveness (to size
certificates and skip dead stores) and reverse postorder.
-/

namespace IxCC.Xv.Alloc.AllSlots

open IxCC.Lir (VReg Label Operand Kind Pos Con)

structure St where
  homes : Std.HashMap VReg Loc := {}
  nextSlot : Nat := 0
  edits : Array (Array (Nat × Edit))
  head : Array (Array Edit)
  locs : Array (Array (List Loc))
  termLocs : Array (List Loc)
  certs : Array (Option (List (Loc × List VReg)))

abbrev M := StateT St (Except String)

def homeOf (v : VReg) : M Loc := do
  match (← get).homes[v]? with
  | some l => pure l
  | none =>
      modifyGet fun s =>
        (.slot s.nextSlot, { s with homes := s.homes.insert v (.slot s.nextSlot), nextSlot := s.nextSlot + 1 })

/-- Sequence a parallel move; `busy` registers are not free as scratch. -/
def resolve (moves : Array (Loc × Loc)) (busy : List X86.GPR) : M (Array Edit) := do
  if moves.isEmpty then return #[]
  let used := moves.toList.flatMap fun (d, s) =>
    (match d with | .reg r => [r] | _ => []) ++ (match s with | .reg r => [r] | _ => [])
  let free := scratch.filter fun r => !busy.contains r && !used.contains r
  let (edits, u) := ParMove.resolve moves
    { free, cycleSlot := .slot 1000000000, victim := .r11, saveSlot := .slot 1000000001 }
  if u.cycleSlot || u.saveSlot then throw "all slots: no scratch register for a parallel move"
  return edits

/-- Locations of one instruction's operands, the loads before it, and the
stores its register definitions need afterwards. -/
def place (ops : List (Operand VReg)) (isMove : Bool) (live : VReg → Bool) :
    M (List Loc × Array (Loc × Loc) × Array (Loc × Loc)) := do
  let opsA := ops.toArray
  let fixedRegs : List X86.GPR := ops.filterMap fun o => match o.con with | .fixed r => some r | _ => none
  let mut pool := scratch.filter (!fixedRegs.contains ·)
  let mut loaded : Std.HashMap VReg X86.GPR := {}
  let mut locs : Array Loc := #[]
  let mut loads : Array (Loc × Loc) := #[]
  let mut stores : Array (Loc × Loc) := #[]
  let tied : List Nat := ops.filterMap fun o => match o.con with | .reuse k => some k | _ => none
  -- Registers for ties first, so their uses and definitions agree.
  let mut tieReg : Std.HashMap Nat X86.GPR := {}
  for k in tied do
    match pool with
    | r :: rest =>
        pool := rest
        tieReg := tieReg.insert k r
        loads := loads.push (.reg r, ← homeOf opsA[k]!.v)
    | [] => throw "all slots: out of registers"
  for (o, j) in ops.zipIdx do
    let v := o.v
    if o.kind == .use then
      match o.con with
      | .fixed r =>
          locs := locs.push (.reg r)
          loads := loads.push (.reg r, ← homeOf v)
      | .stack =>
          locs := locs.push (Xl.argLoc j)
          loads := loads.push (Xl.argLoc j, ← homeOf v)
      | _ =>
          if let some r := tieReg[j]? then locs := locs.push (.reg r)
          else if o.con == .reg || isMove then
            match loaded[v]? with
            | some r => locs := locs.push (.reg r)
            | none =>
                match pool with
                | r :: rest =>
                    pool := rest
                    loaded := loaded.insert v r
                    locs := locs.push (.reg r)
                    loads := loads.push (.reg r, ← homeOf v)
                | [] => throw "all slots: out of registers"
          else locs := locs.push (← homeOf v)
    else
      match o.con with
      | .fixed r =>
          locs := locs.push (.reg r)
          if live v then stores := stores.push (← homeOf v, .reg r)
      | .reuse k =>
          let r := tieReg[k]!
          locs := locs.push (.reg r)
          if live v then stores := stores.push (← homeOf v, .reg r)
      | .any => locs := locs.push (← homeOf v)
      | .reg =>
          match pool with
          | r :: rest =>
              pool := rest
              locs := locs.push (.reg r)
              if live v then stores := stores.push (← homeOf v, .reg r)
          | [] => throw "all slots: out of registers"
      | .stack => throw "all slots: a stack definition (more than two results)"
  return (locs.toList, loads, stores)

def regsOf (ls : List Loc) : List X86.GPR := ls.filterMap fun | .reg r => some r | _ => none

/-- Allocate `f` with every register in its home. -/
def run (f : Func VReg) : Except String Output := do
  let n := f.blocks.size
  if n == 0 then throw "a function without blocks"
  let info := analyse f
  if info.order.size != n then throw "unreachable blocks"
  let uses := f.blocks.map usePositions
  let liveAfter (b : Label) (i : Nat) (v : VReg) : Bool :=
    info.liveOut[b]!.contains v || ((uses[b]!)[v]?.map (·.any (· > i))).getD false
  let mut homes : Std.HashMap VReg Loc := {}
  for (p, i) in f.params.zipIdx do
    if i ≥ Xl.nArgRegs then homes := homes.insert p (Xl.paramLoc i)
  let st : St := { homes, edits := Array.replicate n #[], head := Array.replicate n #[]
                   locs := Array.replicate n #[], termLocs := Array.replicate n []
                   certs := Array.replicate n none }
  let go : M Unit := do
    -- The entry: parameters from their convention locations to their homes.
    let mut entryMoves : Array (Loc × Loc) := #[]
    let mut entryCert : List (Loc × List VReg) := []
    for (p, i) in f.params.zipIdx do
      entryCert := entryCert ++ [(Xl.paramLoc i, [p])]
      if info.liveIn[0]!.contains p then
        let h ← homeOf p
        if h != Xl.paramLoc i then entryMoves := entryMoves.push (h, Xl.paramLoc i)
    let es ← resolve entryMoves []
    modify fun s => { s with head := s.head.set! 0 es, certs := s.certs.set! 0 (some entryCert) }
    for b in info.order do
      let block := f.blocks[b]!
      let nb := block.body.size
      let mut pending : Array (Loc × Loc) := #[]
      let mut pendingRegs : List X86.GPR := []
      let mut locs : Array (List Loc) := #[]
      for i in [:nb + 1] do
        let (ops, isMove) := if h : i < nb then
            (block.body[i].operands, match block.body[i] with | .move .. => true | _ => false)
          else (block.term.operands, false)
        let (ls, loads, stores) ← place ops isMove (liveAfter b i)
        let stored ← resolve pending (pendingRegs ++ regsOf ls)
        let es := stored ++ (← resolve loads (regsOf ls))
        modify fun s => { s with edits := s.edits.modify b fun a => a ++ es.map ((i, ·)) }
        if i < nb then
          locs := locs.push ls
          pending := stores
          pendingRegs := regsOf ls
        else
          modify fun s => { s with locs := s.locs.set! b locs, termLocs := s.termLocs.set! b ls }
          pending := stores
      -- The exit: homes, and the terminator's register definitions.
      let edges := block.term.edges
      for e in edges do
        let s := e.target
        let some target := f.blocks[s]? | throw s!"block {b}: edge to missing block {s}"
        let unique := info.preds[s]!.length == 1
        if !unique && edges.length != 1 then throw s!"block {b}: critical edge to block {s}"
        let live := info.liveIn[s]!
        -- Where a register is at the end of `b`: its pending register, else home.
        let exitLoc (v : VReg) : M Loc := do
          let h ← homeOf v
          match pending.find? (·.1 == h) with
          | some (_, r) => pure r
          | none => pure h
        let mut moves : Array (Loc × Loc) := #[]
        let mut cert : List (Loc × List VReg) := []
        for v in live.toList do
          if target.params.contains v then continue
          let src ← exitLoc v
          let h ← homeOf v
          if src != h then moves := moves.push (h, src)
          cert := (src, [v]) :: cert
        for (p, a) in target.params.zip e.args do
          if !live.contains p then continue
          let src ← exitLoc a
          let h ← homeOf p
          if src != h then moves := moves.push (h, src)
          cert := (src, [p]) :: cert
        let homeCert ← (live.toList).mapM fun v => do return (← homeOf v, [v])
        if (← get).certs[s]!.isNone then
          modify fun st => { st with certs := st.certs.set! s (some (if unique then cert else homeCert)) }
        let es ← resolve moves (regsOf (pending.toList.map (·.2)))
        if unique then modify fun st => { st with head := st.head.set! s es }
        else modify fun st => { st with edits := st.edits.modify b fun a => a ++ es.map ((nb, ·)) }
  let ((), st) ← go.run st
  let blocks := (List.range n).map fun b =>
    { locs := st.locs[b]!.toList, termLocs := st.termLocs[b]!
      edits := (st.head[b]!.map ((0, ·))).toList ++ st.edits[b]!.toList
      cert := (st.certs[b]!).getD [] : BlockOut }
  return { blocks, numSlots := st.nextSlot }

end IxCC.Xv.Alloc.AllSlots
