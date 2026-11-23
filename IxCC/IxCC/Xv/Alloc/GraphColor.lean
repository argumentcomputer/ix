import IxCC.Xv.Alloc.Interference

/-!
# Chaitin-Briggs / Iterated Register Coalescing (IRC) graph-coloring allocator (untrusted)

Allocates an Xv function in three phases:

1. **Interference & move graph** (`buildGraph` in `Interference.lean`): exact
   backward dataflow liveness, natural loop depth, loop-weighted spill costs,
   call-result deferral ranges, and instruction-accurate interference + move
   edges (respecting caller-saved clobbers, custom runtime clobbers, fixed
   register constraints, early defs, late uses, `.reuse` ties, and block-param
   parallel copies).
2. **Iterated Register Coalescing (`colorGraph`)**: George-Appel worklist loop
   (Simplify, George/Briggs conservative Coalesce ordered by descending loop
   weight, Freeze, and optimistic Chaitin-Briggs SelectSpill minimizing
   `weight / degree`), followed by biased LIFO color assignment (`assignColors`,
   preferring caller-saved and RC-saved registers before callee-saved ones) and
   graph-coloring spill-slot reuse (`assignSpillSlots`) with spill-move biasing.
3. **Color-guided materialization (`materialize`)**: emits a concrete
   `Alloc.Output` (operand locations, parallel-move edits, and block entry
   certificates). Multi-predecessor join blocks and loop headers adopt IRC's
   globally coalesced coloring directly; single-predecessor blocks and
   deferred call results preserve lazy placement so base-case paths pay zero
   extra moves and recursive functions like `fib` minimize callee-saved saves.

Everything here is untrusted producer code (`Xv.Validate.func` checks the result,
with `Driver.lean` falling back to `LinearScan` and `AllSlots`), and every loop
is explicitly fuel-bounded (zero `partial`). -/

namespace IxCC.Xv.Alloc.GraphColor

open IxCC.Lir (VReg Label FunId Operand Kind Pos Con)

/-! ## Phase 2: Iterated Register Coalescing (George-Appel) -/

private inductive NodeState where
  | precolored
  | simplify
  | freeze
  | spill
  | coalesced
  | stacked
  deriving DecidableEq, Inhabited

private inductive MoveState where
  | worklist
  | active
  | coalesced
  | constrained
  | frozen
  deriving DecidableEq, Inhabited

@[inline] private def NodeState.isActive : NodeState → Bool
  | .simplify | .freeze | .spill => true
  | _ => false

/-- Result of IRC graph coloring + spill-slot coloring. -/
structure ColorResult where
  /-- Assigned GPR color `0..12`, or `none` if spilled. -/
  color : Array (Option Nat)
  /-- Assigned frame slot `0..numSpillSlots-1` for spilled non-`inArg` nodes. -/
  slot : Array (Option Nat)
  numSpillSlots : Nat
  coalescedMoves : Nat
  deriving Inhabited

private structure IrcSt where
  preMask : Array UInt16
  adjList : Array (Array Nat)
  adjSet : Std.HashSet UInt64
  deg : Array Nat
  weight : Array Nat
  alias : Array Nat
  status : Array NodeState
  moveStatus : Array MoveState
  nodeMoves : Array (Array Nat)
  simplifyWL : Array Nat := #[]
  freezeWL : Array Nat := #[]
  spillWL : Array Nat := #[]
  moveWL : Array Nat := #[]
  selectStack : Array Nat := #[]
  coalescedCount : Nat := 0
  rng : UInt64 := 0

private def getAlias (alias : Array Nat) (status : Array NodeState) (u : Nat) : Nat := Id.run do
  let mut x := u
  for _ in [:alias.size] do
    if status[x]! == .coalesced then
      x := alias[x]!
    else
      break
  return x

private def isMoveRelated (s : IrcSt) (u : Nat) : Bool :=
  s.nodeMoves[u]!.any fun mi =>
    let ms := s.moveStatus[mi]!
    ms == .worklist || ms == .active

private def enableNodeMoves (s : IrcSt) (u : Nat) : IrcSt := Id.run do
  let mut moveStatus := s.moveStatus
  let mut moveWL := s.moveWL
  for mi in s.nodeMoves[u]! do
    if moveStatus[mi]! == .active then
      moveStatus := moveStatus.set! mi .worklist
      moveWL := moveWL.push mi
  return { s with moveStatus, moveWL }

private def enableMovesAround (s : IrcSt) (m : Nat) : IrcSt := Id.run do
  let mut s := enableNodeMoves s m
  for t in s.adjList[m]! do
    if s.status[t]!.isActive then
      s := enableNodeMoves s t
  return s

private def decrementDegree (s : IrcSt) (m : Nat) : IrcSt :=
  if isPrecolored m || !s.status[m]!.isActive then s
  else
    let d := s.deg[m]!
    let s := { s with deg := s.deg.set! m (d - 1) }
    if d == K then
      let s := enableMovesAround s m
      if isMoveRelated s m then
        { s with status := s.status.set! m .freeze, freezeWL := s.freezeWL.push m }
      else
        { s with status := s.status.set! m .simplify, simplifyWL := s.simplifyWL.push m }
    else s

private def addWorklist (s : IrcSt) (u : Nat) : IrcSt :=
  if !isPrecolored u && s.status[u]! == .freeze && !isMoveRelated s u && s.deg[u]! < K then
    { s with status := s.status.set! u .simplify, simplifyWL := s.simplifyWL.push u }
  else s

private def ircInterferes (s : IrcSt) (u v : Nat) : Bool :=
  if u == v then true
  else if isPrecolored u then
    if isPrecolored v then true else (s.preMask[v]! &&& colorBit u) != 0
  else if isPrecolored v then
    (s.preMask[u]! &&& colorBit v) != 0
  else
    s.adjSet.contains (edgeKey u v)

/-- George criterion for coalescing non-precolored `v` into precolored `c`. -/
private def okGeorge (s : IrcSt) (c v : Nat) : Bool :=
  s.adjList[v]!.all fun t =>
    if !s.status[t]!.isActive then true
    else (s.preMask[t]! &&& colorBit c) != 0 || s.deg[t]! < K

/-- Exact Briggs criterion for coalescing two non-precolored nodes `u` and `v`
(accounting for common neighbors whose degree drops by 1). -/
private def conservativeBriggs (s : IrcSt) (u v : Nat) : Bool := Id.run do
  let mut sig := popcount13 (s.preMask[u]! ||| s.preMask[v]!)
  if sig ≥ K then return false
  for t in s.adjList[u]! do
    if s.status[t]!.isActive then
      let common := s.adjSet.contains (edgeKey v t)
      let eff := if common then s.deg[t]! - 1 else s.deg[t]!
      if eff ≥ K then
        sig := sig + 1
        if sig ≥ K then return false
  for t in s.adjList[v]! do
    if s.status[t]!.isActive && !s.adjSet.contains (edgeKey u t) then
      if s.deg[t]! ≥ K then
        sig := sig + 1
        if sig ≥ K then return false
  return sig < K

/-- Merge non-precolored `v` into `u` (which may be precolored or virtual). -/
private def combine (s : IrcSt) (u v : Nat) : IrcSt := Id.run do
  let mut s := { s with
    status := s.status.set! v .coalesced
    alias := s.alias.set! v u
    coalescedCount := s.coalescedCount + 1 }
  -- Re-enable active moves of `v` so they are re-evaluated against `u`.
  s := enableNodeMoves s v
  if !isPrecolored u then
    let mut uMoves := s.nodeMoves[u]!
    for mi in s.nodeMoves[v]! do
      let ms := s.moveStatus[mi]!
      if ms == .worklist || ms == .active then
        uMoves := uMoves.push mi
    s := { s with
      nodeMoves := s.nodeMoves.set! u uMoves
      weight := s.weight.modify u (· + s.weight[v]!) }
  let vAdj := s.adjList[v]!
  if isPrecolored u then
    for t in vAdj do
      if s.status[t]!.isActive then
        if (s.preMask[t]! &&& colorBit u) == 0 then
          s := { s with preMask := s.preMask.modify t (· ||| colorBit u) }
        else
          s := decrementDegree s t
  else
    let addedPre := s.preMask[v]! &&& (allColorsMask ^^^ s.preMask[u]!)
    s := { s with
      preMask := s.preMask.modify u (· ||| s.preMask[v]!)
      deg := s.deg.modify u (· + popcount13 addedPre) }
    for t in vAdj do
      if s.status[t]!.isActive && t != u then
        let k := edgeKey u t
        if s.adjSet.contains k then
          s := decrementDegree s t
        else
          s := { s with
            adjSet := s.adjSet.insert k
            adjList := (s.adjList.modify u (·.push t)).modify t (·.push u)
            deg := s.deg.modify u (· + 1) }
    if s.deg[u]! ≥ K && (s.status[u]! == .freeze || s.status[u]! == .simplify) then
      s := { s with status := s.status.set! u .spill, spillWL := s.spillWL.push u }
  return s

private def freezeNode (s : IrcSt) (moves : Array MoveEdge) (u : Nat) : IrcSt := Id.run do
  let mut s := { s with
    status := s.status.set! u .simplify
    simplifyWL := s.simplifyWL.push u }
  for mi in s.nodeMoves[u]! do
    let ms := s.moveStatus[mi]!
    if ms == .active || ms == .worklist then
      s := { s with moveStatus := s.moveStatus.set! mi .frozen }
      let m := moves[mi]!
      let a := getAlias s.alias s.status m.u
      let b := getAlias s.alias s.status m.v
      let other := if a == u then b else a
      if !isPrecolored other && s.status[other]! == .freeze && !isMoveRelated s other then
        s := { s with status := s.status.set! other .simplify, simplifyWL := s.simplifyWL.push other }
  return s

private def ircChance (rng : UInt64) (p : Nat) : Bool × UInt64 :=
  if p == 0 then (false, rng)
  else
    let t := rng + 0x9e3779b97f4a7c15
    ((mix64 t).toNat % 100 < p, t)

/-- Run George-Appel IRC and spill-slot coloring on `g`. -/
def colorGraph (g : Graph) (chaos : Chaos) (rng0 : UInt64) : ColorResult := Id.run do
  let n := g.numNodes
  let moves := g.moves
  let mut deg : Array Nat := Array.replicate n 0
  for c in [:K] do deg := deg.set! c 1000000
  for u in [K : n] do
    deg := deg.set! u (popcount13 g.preMask[u]! + g.adjList[u]!.size)
  let origDeg := deg

  let mut nodeMoves : Array (Array Nat) := Array.replicate n #[]
  for h : mi in [:moves.size] do
    let m := moves[mi]
    nodeMoves := (nodeMoves.modify m.u (·.push mi)).modify m.v (·.push mi)

  let mut status : Array NodeState := Array.replicate n .simplify
  let mut simplifyWL : Array Nat := #[]
  let mut freezeWL : Array Nat := #[]
  let mut spillWL : Array Nat := #[]
  for c in [:K] do status := status.set! c .precolored
  for u in [K : n] do
    if deg[u]! ≥ K then
      status := status.set! u .spill
      spillWL := spillWL.push u
    else if !nodeMoves[u]!.isEmpty then
      status := status.set! u .freeze
      freezeWL := freezeWL.push u
    else
      status := status.set! u .simplify
      simplifyWL := simplifyWL.push u

  -- Pop from the back so highest-weight move (`moves[0]`) is tried first.
  let moveWL : Array Nat := Array.ofFn (n := moves.size) fun i => moves.size - 1 - i.val
  let alias : Array Nat := Array.ofFn (n := n) fun i => i.val
  let mut s : IrcSt := {
    preMask := g.preMask
    adjList := g.adjList
    adjSet := g.adjSet
    deg
    weight := g.weight
    alias
    status
    moveStatus := Array.replicate moves.size .worklist
    nodeMoves
    simplifyWL
    freezeWL
    spillWL
    moveWL
    rng := rng0
  }

  -- Main IRC loop (total, fuel-bounded).
  let fuel := 6 * n + 6 * moves.size + 32
  for _ in [:fuel] do
    -- 1. Simplify: pop next active low-degree non-move-related node.
    let mut didStep := false
    for _ in [:s.simplifyWL.size] do
      match s.simplifyWL.back? with
      | none => break
      | some u =>
          s := { s with simplifyWL := s.simplifyWL.pop }
          if s.status[u]! == .simplify then
            s := { s with
              status := s.status.set! u .stacked
              selectStack := s.selectStack.push u }
            for m in s.adjList[u]! do
              if s.status[m]!.isActive then
                s := decrementDegree s m
            didStep := true
            break
    if didStep then continue

    -- 2. Coalesce: pop next worklist move.
    for _ in [:s.moveWL.size] do
      match s.moveWL.back? with
      | none => break
      | some mi =>
          s := { s with moveWL := s.moveWL.pop }
          if s.moveStatus[mi]! == .worklist then
            let m := moves[mi]!
            let x := getAlias s.alias s.status m.u
            let y := getAlias s.alias s.status m.v
            let (u, v) := if isPrecolored y then (y, x) else (x, y)
            let (skipChaos, rng') := ircChance s.rng chaos.ignoreHint
            s := { s with rng := rng' }
            if u == v then
              s := { s with moveStatus := s.moveStatus.set! mi .coalesced }
              s := addWorklist s u
            else if isPrecolored v || ircInterferes s u v then
              s := { s with moveStatus := s.moveStatus.set! mi .constrained }
              s := addWorklist s u
              s := addWorklist s v
            else if skipChaos then
              s := { s with moveStatus := s.moveStatus.set! mi .frozen }
              s := addWorklist s u
              s := addWorklist s v
            else if (isPrecolored u && okGeorge s u v) || (!isPrecolored u && conservativeBriggs s u v) then
              s := { s with moveStatus := s.moveStatus.set! mi .coalesced }
              s := combine s u v
              s := addWorklist s u
            else
              s := { s with moveStatus := s.moveStatus.set! mi .active }
            didStep := true
            break
    if didStep then continue

    -- 3. Freeze: pick lowest move-weight active node in `freezeWL`.
    if !s.freezeWL.isEmpty then
      let mut liveFreeze : Array Nat := #[]
      let mut bestNode : Option Nat := none
      let mut bestW : Nat := 0
      for u in s.freezeWL do
        if s.status[u]! == .freeze then
          liveFreeze := liveFreeze.push u
          let mut mw := 0
          for mi in s.nodeMoves[u]! do
            let ms := s.moveStatus[mi]!
            if ms == .active || ms == .worklist then mw := mw + moves[mi]!.weight
          match bestNode with
          | none => bestNode := some u; bestW := mw
          | some bn =>
              if mw < bestW || (mw == bestW && u < bn) then
                bestNode := some u; bestW := mw
      s := { s with freezeWL := liveFreeze }
      if let some u := bestNode then
        s := freezeNode s moves u
        continue

    -- 4. SelectSpill: pick active high-degree node with lowest `weight / deg`.
    if !s.spillWL.isEmpty then
      let mut liveSpill : Array Nat := #[]
      for u in s.spillWL do
        if s.status[u]! == .spill then liveSpill := liveSpill.push u
      s := { s with spillWL := liveSpill }
      if !liveSpill.isEmpty then
        let (randPick, rng') := ircChance s.rng chaos.randomVictim
        s := { s with rng := rng' }
        let chosen : Nat ←
          if randPick then
            let t := s.rng + 0x9e3779b97f4a7c15
            s := { s with rng := t }
            pure liveSpill[(mix64 t).toNat % liveSpill.size]!
          else
            let mut best := liveSpill[0]!
            let mut bestW := s.weight[best]!
            let mut bestD := max 1 (s.deg[best]! + origDeg[best]!)
            for idx in [1 : liveSpill.size] do
              let u := liveSpill[idx]!
              let wu := s.weight[u]!
              let du := max 1 (s.deg[u]! + origDeg[u]!)
              if wu * bestD < bestW * du || (wu * bestD == bestW * du && u < best) then
                best := u; bestW := wu; bestD := du
            pure best
        s := { s with
          status := s.status.set! chosen .stacked
          selectStack := s.selectStack.push chosen }
        for m in s.adjList[chosen]! do
          if s.status[m]!.isActive then
            s := decrementDegree s m
        continue

    -- All worklists empty!
    break

  -- Safety net: if anything remained active (should not happen), push onto stack.
  for u in [K : n] do
    if s.status[u]!.isActive then
      s := { s with status := s.status.set! u .stacked, selectStack := s.selectStack.push u }

  -- Color preference order: caller-saved (including RC-saved) first, then callee-saved.
  let prefOrder : List Nat :=
    if chaos.shuffle then
      ((List.range K).toArray.qsort fun a b =>
        let ha := mix64 (rng0 + UInt64.ofNat a)
        let hb := mix64 (rng0 + UInt64.ofNat b)
        ha < hb || (ha == hb && a < b)).toList
    else
      List.range K

  -- Under chaos with `regLimit < K`, restrict preferred colors to stress spilling.
  let limitOrder := prefOrder.take (max 1 chaos.regLimit)
  let limitMask : UInt16 := limitOrder.foldl (fun m c => m ||| colorBit c) 0

  -- Select phase: pop `selectStack` LIFO with biased coloring.
  let mut color : Array (Option Nat) := Array.replicate n none
  for c in [:K] do color := color.set! c (some c)

  for idx in [:s.selectStack.size] do
    let u := s.selectStack[s.selectStack.size - 1 - idx]!
    let mut used : UInt16 := s.preMask[u]!
    for w in s.adjList[u]! do
      let a := getAlias s.alias s.status w
      if let some c := color[a]! then
        used := used ||| colorBit c

    -- Biased coloring: prefer the highest-weight already-colored move partner's color.
    let mut biased : Option Nat := none
    let mut bestBiasW : Nat := 0
    let (ignoreBias, rng') := ircChance s.rng chaos.ignoreHint
    s := { s with rng := rng' }
    if !ignoreBias then
      for mi in s.nodeMoves[u]! do
        let m := moves[mi]!
        let a := getAlias s.alias s.status m.u
        let b := getAlias s.alias s.status m.v
        let other := if a == u then b else a
        if let some c := color[other]! then
          if (used &&& colorBit c) == 0 && (!chaos.enabled || (limitMask &&& colorBit c) != 0) then
            if biased.isNone || m.weight > bestBiasW then
              biased := some c
              bestBiasW := m.weight

    let chosen : Option Nat := match biased with
      | some c => some c
      | none =>
          match limitOrder.find? fun c => (used &&& colorBit c) == 0 with
          | some c => some c
          | none =>
              if chaos.enabled && chaos.regLimit < K then none
              else prefOrder.find? fun c => (used &&& colorBit c) == 0
    color := color.set! u chosen

  -- Propagate colors to coalesced nodes.
  for u in [K : n] do
    if s.status[u]! == .coalesced then
      let a := getAlias s.alias s.status u
      color := color.set! u color[a]!

  -- Phase 2b: Graph-coloring spill-slot reuse using full un-deferred interference
  -- (so two simultaneously-live spilled values never share a slot even if one was deferred),
  -- with biased spill-slot coalescing across move-related spilled partners.
  let mut spilledNodes : Array Nat := #[]
  let mut isSpilled : Array Bool := Array.replicate n false
  for u in [K : n] do
    if color[u]!.isNone && g.inArgIdx[u]!.isNone then
      spilledNodes := spilledNodes.push u
      isSpilled := isSpilled.set! u true

  let mut spillDeg : Array Nat := Array.replicate n 0
  for u in spilledNodes do
    let mut d := 0
    for w in g.adjList[u]! do
      if isSpilled[w]! then d := d + 1
    spillDeg := spillDeg.set! u d
  spilledNodes := spilledNodes.qsort fun a b =>
    spillDeg[a]! > spillDeg[b]! ||
      (spillDeg[a]! == spillDeg[b]! && (g.weight[a]! > g.weight[b]! || (g.weight[a]! == g.weight[b]! && a < b)))

  let mut slot : Array (Option Nat) := Array.replicate n none
  let mut slotGroups : Array (Array Nat) := #[]
  let mut numSpillSlots : Nat := 0
  for u in spilledNodes do
    let slotFits (k : Nat) : Bool :=
      (slotGroups[k]!).all fun w => !g.interferesFull u w
    -- Biased spill-slot reuse: prefer the slot of a non-interfering move partner.
    let mut picked : Option Nat := none
    if !chaos.enabled then
      let mut bestW := 0
      for mi in nodeMoves[u]! do
        let m := moves[mi]!
        let other := if m.u == u then m.v else m.u
        if let some k := slot[other]! then
          if slotFits k && (picked.isNone || m.weight > bestW) then
            picked := some k
            bestW := m.weight
    let k ← match picked with
      | some k => pure k
      | none =>
          let mut found := numSpillSlots
          if !chaos.enabled then
            for cand in [:numSpillSlots] do
              if slotFits cand then
                found := cand
                break
          pure found
    slot := slot.set! u (some k)
    if k ≥ numSpillSlots then
      slotGroups := slotGroups.push #[u]
      numSpillSlots := k + 1
    else
      slotGroups := slotGroups.modify k (·.push u)

  return { color, slot, numSpillSlots, coalescedMoves := s.coalescedCount }

/-! ## Phase 3: Color-guided materialization into `Alloc.Output` -/

private structure MCfg where
  f : Func VReg
  g : Graph
  col : ColorResult
  env : Xl.Env
  chaos : Chaos
  order : List X86.GPR

private structure MSt where
  homes : Std.HashMap VReg Loc := {}
  slotRemap : Std.HashMap Nat Nat := {}
  slotOwners : Array (List Nat) := #[]
  nextSlot : Nat := 0
  cycleSlot : Option Nat := none
  saveSlot : Option Nat := none
  rng : UInt64
  edits : Array (Array (Nat × Edit))
  locs : Array (Array (List Loc))
  termLocs : Array (List Loc)
  certs : Array (Option (List (Loc × List VReg)))
  entry : Array (Option RState)
  cur : RState := {}

private abbrev M := ReaderT MCfg (StateT MSt (Except String))

private def rand : M UInt64 :=
  modifyGet fun s => let t := s.rng + 0x9e3779b97f4a7c15; (mix64 t, { s with rng := t })

private def chance (p : Nat) : M Bool := do
  if p == 0 then return false
  return (← rand).toNat % 100 < p

private def pickOne {α : Type} [Inhabited α] (xs : List α) : M α := do
  return xs[(← rand).toNat % xs.length]!

private def targetRegOf (v : VReg) : M (Option X86.GPR) := do
  let cfg ← read
  match cfg.g.vregToNode[v]? with
  | some u => return (cfg.col.color[u]!).map (colorRegs[·]!)
  | none => return none

private def isCrossCall (v : VReg) : M Bool := do
  let cfg ← read
  match cfg.g.vregToNode[v]? with
  | some u => return cfg.g.crossCall[u]!
  | none => return false

private def clobMaskOf (v : VReg) : M UInt16 := do
  let cfg ← read
  match cfg.g.vregToNode[v]? with
  | some u => return cfg.g.callClobMask[u]!
  | none => return 0

private def mustRegOf (v : VReg) : M Bool := do
  let cfg ← read
  match cfg.g.vregToNode[v]? with
  | some u => return cfg.g.mustReg[u]!
  | none => return false

private def weightOf (v : VReg) : M Nat := do
  let cfg ← read
  match cfg.g.vregToNode[v]? with
  | some u => return cfg.g.weight[u]!
  | none => return 1

/-- Home cell of `v`: its incoming stack arg, its lazily materialized IRC-colored
spill slot, or a fresh/reused non-interfering frame slot. -/
private def homeOf (v : VReg) : M Loc := do
  match (← get).homes[v]? with
  | some l => pure l
  | none =>
      let cfg ← read
      let s ← get
      let uOpt := cfg.g.vregToNode[v]?
      -- First check if IRC assigned a colored spill slot for `v`.
      if !cfg.chaos.enabled then
        if let some u := uOpt then
          if let some ircSlot := cfg.col.slot[u]! then
            match s.slotRemap[ircSlot]? with
            | some k =>
                if (s.slotOwners[k]!).all fun w => !cfg.g.interferesFull w u then
                  set { s with homes := s.homes.insert v (.slot k)
                               slotOwners := s.slotOwners.modify k (u :: ·) }
                  return .slot k
            | none =>
                let k := s.nextSlot
                let owners := (s.slotOwners ++ Array.replicate (k + 1 - s.slotOwners.size) []).set! k [u]
                set { s with homes := s.homes.insert v (.slot k)
                             slotRemap := s.slotRemap.insert ircSlot k
                             slotOwners := owners
                             nextSlot := k + 1 }
                return .slot k
          -- Otherwise try reusing any non-interfering allocated slot.
          if let some k := (List.range s.nextSlot).find? fun k =>
              match s.slotOwners[k]? with
              | some os => !os.isEmpty && os.all fun w => !cfg.g.interferesFull w u
              | none => false then
            let owners := u :: s.slotOwners[k]!
            set { s with homes := s.homes.insert v (.slot k), slotOwners := s.slotOwners.set! k owners }
            return .slot k
      let k := s.nextSlot
      let owners := (s.slotOwners ++ Array.replicate (k + 1 - s.slotOwners.size) []).set! k (uOpt.toList)
      set { s with homes := s.homes.insert v (.slot k), slotOwners := owners, nextSlot := k + 1 }
      return .slot k

private def srcIn (s : RState) (v : VReg) : M Loc :=
  match s.reg[v]? with
  | some r => pure (.reg r)
  | none => if s.home.contains v then homeOf v else throw s!"v{v} has no location"

private def liveAfter (b : Label) (i : Nat) (v : VReg) : M Bool := do
  let cfg ← read
  if cfg.g.liveOut[b]!.contains v then return true
  match cfg.g.uses[b]![v]? with
  | some ps => return ps.any (· > i)
  | none => return false

private def nextUse (b : Label) (i : Nat) (v : VReg) : M Nat := do
  let cfg ← read
  let n := cfg.f.blocks[b]!.body.size
  match (cfg.g.uses[b]![v]?).bind (·.find? (· > i)) with
  | some j => return j - i
  | none => return n + 1 - i + 64

/-- Preference order for picking a register when the IRC target color is unavailable. -/
private def orderFor (acrossCall : Bool) (v : Option VReg := none) : M (List X86.GPR) := do
  let cfg ← read
  let o := cfg.order
  if acrossCall then
    let base := if cfg.chaos.shuffle then
        o.filter calleeSavedRegs.contains ++
          o.filter rcSavedRegs.contains ++
          o.filter (fun r => !calleeSavedRegs.contains r && !rcSavedRegs.contains r)
      else crossCallOrder
    let cm ← match v with
      | some u => clobMaskOf u
      | none => pure 0
    if cm == 0 then return base
    else
      let survives (r : X86.GPR) : Bool :=
        match gprToColor r with | some c => (cm &&& colorBit c) == 0 | none => false
      return base.filter survives ++ base.filter (!survives ·)
  return o

private def pickReg (ok : X86.GPR → Bool) (hint : Option X86.GPR) (acrossCall : Bool)
    (v : Option VReg := none) : M (Option X86.GPR) := do
  let cfg ← read
  if let some h := hint then
    if ok h && !(← chance cfg.chaos.ignoreHint) then return some h
  let base ← orderFor acrossCall v
  match (base.take cfg.chaos.regLimit).find? ok with
  | some r => return some r
  | none => return base.find? ok

private def chooseScratch (free : List X86.GPR) (holding : X86.GPR → Bool) : M (List X86.GPR × X86.GPR) := do
  let cfg ← read
  let victims := scratch.filter fun r => holding r && !free.contains r
  let free := if !victims.isEmpty && (← chance cfg.chaos.noFreeScratch) then [] else free
  let victim ← match victims with
    | [] => pure (free.headD .r11)
    | v :: _ => if cfg.chaos.randomVictim > 0 then pickOne victims else pure v
  return (free, victim)

/-! ### Per-instruction placement -/

private structure Plan where
  b : Label
  i : Nat
  st : RState
  usedHere : Std.HashSet VReg
  needMid : Array (Option VReg) := Array.replicate 16 none
  after : Array (Option VReg) := Array.replicate 16 none
  homeAfter : Std.HashSet VReg
  moves : Array (Loc × Loc) := #[]
  blocked : Array Bool := Array.replicate 16 false
  fixedReg : Array Bool := Array.replicate 16 false
  fixedUse : Array (Option VReg) := Array.replicate 16 none

private abbrev P := StateT Plan M

@[inline] private def ix (r : X86.GPR) : Nat := gprIndex r

private def addMove (dst src : Loc) : P Unit :=
  if dst == src then pure () else modify fun p => { p with moves := p.moves.push (dst, src) }

/-- Evict a surviving register not used by this instruction. Prefers values IRC
spilled or values already stored in their home cell. -/
private def evict (ok : X86.GPR → Bool) : P (Option X86.GPR) := do
  let p ← get
  let mut cands : Array (X86.GPR × VReg) := #[]
  for r in scratch do
    match p.after[ix r]!, p.needMid[ix r]! with
    | some u, some u' =>
        if u == u' && p.st.get r == some u && !p.usedHere.contains u && !p.fixedReg[ix r]! &&
            !p.blocked[ix r]! && ok r then
          cands := cands.push (r, u)
    | _, _ => pure ()
  if cands.isEmpty then return none
  let chaos := (← read).chaos
  let (r, u) ← if ← chance chaos.randomVictim then pickOne cands.toList else do
    let mut best := cands[0]!
    let mut bestKey := (0 : Nat)
    let mut first := true
    for (r, u) in cands do
      let d ← nextUse p.b p.i u
      let w ← weightOf u
      let homed := p.st.home.contains u || p.homeAfter.contains u
      let spilled := (← targetRegOf u).isNone
      let spillTier := if spilled then 0 else 1
      let key := spillTier * 1000000000 + ((w * 1024) / (d + 1)) * 2 + (if homed then 0 else 1)
      if first || key < bestKey then
        best := (r, u)
        bestKey := key
        first := false
    pure best
  if !(p.st.home.contains u || p.homeAfter.contains u) then
    addMove (← homeOf u) (.reg r)
  modify fun p => { p with homeAfter := p.homeAfter.insert u
                           after := p.after.set! (ix r) none
                           needMid := p.needMid.set! (ix r) none }
  return some r

private def grab (hint : Option X86.GPR) (acrossCall : Bool) (v : Option VReg := none) : P X86.GPR := do
  let p ← get
  let ok (r : X86.GPR) : Bool :=
    p.needMid[ix r]!.isNone && p.after[ix r]!.isNone && !p.blocked[ix r]! && !p.fixedReg[ix r]!
  match ← pickReg ok hint acrossCall v with
  | some r => return r
  | none =>
      match ← evict fun _ => true with
      | some r => return r
      | none => throw s!"block {p.b} instruction {p.i}: no register is free"

private def grabLate (hint : Option X86.GPR) (acrossCall : Bool) (preferDying : Bool)
    (v : Option VReg := none) : P (Option X86.GPR) := do
  let p ← get
  let ok (r : X86.GPR) : Bool := p.after[ix r]!.isNone && !p.blocked[ix r]! && !p.fixedReg[ix r]!
  let dying := scratch.filter fun r => ok r && p.needMid[ix r]!.isSome
  if preferDying && hint.isNone then
    if let some r := dying.head? then return some r
  match ← pickReg ok hint acrossCall v with
  | some r => return some r
  | none => evict fun _ => true

/-- If `h` holds a surviving value `u` whose own IRC color is `q ≠ h` (or spilled),
move `u` out of `h` to `q` (or its home) so a definition targeting `h` can take it.
When `clearMid` is true (for early defs / ties needing `needMid[h]` free), requires
`u` not to be used by this instruction. -/
private def vacateToHome (h : X86.GPR) (clearMid : Bool) : P Unit := do
  let p ← get
  let some u := p.after[ix h]! | return
  unless p.st.get h == some u && !p.blocked[ix h]! && !p.fixedReg[ix h]! do return
  if clearMid && p.usedHere.contains u then return
  let targetU ← targetRegOf u
  if targetU == some h then return
  match targetU with
  | some q =>
      if p.needMid[ix q]!.isNone && p.after[ix q]!.isNone && !p.blocked[ix q]! && !p.fixedReg[ix q]! then
        addMove (.reg q) (.reg h)
        modify fun p =>
          { p with
            needMid := if clearMid then (p.needMid.set! (ix q) (some u)).set! (ix h) none
                       else p.needMid.set! (ix q) (some u)
            after := (p.after.set! (ix q) (some u)).set! (ix h) none }
  | none =>
      if !(p.st.home.contains u || p.homeAfter.contains u) then
        addMove (← homeOf u) (.reg h)
      modify fun p =>
        { p with
          homeAfter := p.homeAfter.insert u
          needMid := if clearMid then p.needMid.set! (ix h) none else p.needMid
          after := p.after.set! (ix h) none }

private def resolveMoves (moves : Array (Loc × Loc)) (free : List X86.GPR) (victim : X86.GPR) :
    M (Array Edit) := do
  if moves.isEmpty then return #[]
  let cycle : Loc := .slot 1000000000
  let save : Loc := .slot 1000000001
  let (edits, used) := ParMove.resolve moves { free, cycleSlot := cycle, victim, saveSlot := save }
  let mut edits := edits
  if used.cycleSlot then
    let s ← slotFor true
    edits := edits.map (renameLoc cycle (.slot s))
  if used.saveSlot then
    let s ← slotFor false
    edits := edits.map (renameLoc save (.slot s))
  return edits
where
  slotFor (cycle : Bool) : M Nat := do
    let s ← get
    match (if cycle then s.cycleSlot else s.saveSlot) with
    | some n => return n
    | none =>
        let n := s.nextSlot
        set { s with nextSlot := n + 1
                     cycleSlot := if cycle then some n else s.cycleSlot
                     saveSlot := if cycle then s.saveSlot else some n }
        return n
  renameLoc (a b : Loc) : Edit → Edit
    | .move d s => .move (if d == a then b else d) (if s == a then b else s)

private def allocAt (b : Label) (i : Nat) (ops : List (Operand VReg)) (clob : List X86.GPR)
    (isMove : Bool) : M (List Loc) := do
  let cfg ← read
  let st := (← get).cur
  let opsA := ops.toArray
  let usedHere : Std.HashSet VReg := (opUses ops).foldl (·.insert ·) {}
  let tied : List Nat := ops.filterMap fun o => match o.con with | .reuse k => some k | _ => none
  let plan : Plan := { b, i, st, usedHere, homeAfter := st.home }
  let run : P (List Loc) := do
    let mut locs : Array (Option Loc) := Array.replicate ops.length none
    for r in clob do modify fun p => { p with blocked := p.blocked.set! (ix r) true }
    -- 1. Fixed and convention operands.
    for (o, j) in ops.zipIdx do
      match o.con with
      | .fixed r =>
          locs := locs.set! j (some (.reg r))
          if o.kind == .use then
            match (← get).fixedUse[ix r]! with
            | some w => if w != o.v then throw s!"block {b} instruction {i}: two values fixed to {repr r}"
            | none => modify fun p => { p with fixedUse := p.fixedUse.set! (ix r) (some o.v) }
          else modify fun p => { p with blocked := p.blocked.set! (ix r) true }
          modify fun p => { p with fixedReg := p.fixedReg.set! (ix r) true }
      | .stack =>
          if o.kind == .use && !clob.isEmpty then locs := locs.set! j (some (Xl.argLoc j))
          else throw s!"block {b} instruction {i}: a stack operand outside call arguments"
      | _ => pure ()
    for r in scratch do
      if let some v := (← get).fixedUse[ix r]! then
        modify fun p => { p with needMid := p.needMid.set! (ix r) (some v) }
        if st.reg[v]? != some r then addMove (.reg r) (← srcIn st v)
    for (o, j) in ops.zipIdx do
      if o.kind == .use && o.con == .stack then addMove (Xl.argLoc j) (← srcIn st o.v)

    -- 2. Surviving values stay unless their register is needed/clobbered.
    let mut relocate : Array (VReg × X86.GPR) := #[]
    for r in scratch do
      if let some u := st.get r then
        let p ← get
        let readable := p.fixedUse[ix r]!.isNone || p.fixedUse[ix r]! == some u
        if ← liveAfter b i u then
          if !p.blocked[ix r]! && readable then
            set { p with needMid := p.needMid.set! (ix r) (some u), after := p.after.set! (ix r) (some u) }
          else relocate := relocate.push (u, r)
        if readable && usedHere.contains u then
          modify fun p => { p with needMid := p.needMid.set! (ix r) (some u) }

    -- 3. Other uses: `reg` first, then `any`; tied uses go with their definitions.
    let mut useLoc : Std.HashMap VReg Loc := {}
    let order := ops.zipIdx.filter fun (o, j) =>
      o.kind == .use && !tied.contains j && (o.con == .reg || o.con == .any)
    for (o, j) in order.filter (·.1.con == .reg) ++ order.filter (·.1.con == .any) do
      let v := o.v
      let p ← get
      let readable := match st.reg[v]? with
        | some r => if p.fixedUse[ix r]!.isNone || p.fixedUse[ix r]! == some v then some r else none
        | none => none
      let prior := useLoc[v]?
      let loc ← match o.con, prior, readable with
        | .reg, some (.reg r), _ => pure (Loc.reg r)
        | .any, some l, _ => pure l
        | .any, none, some r =>
            if !isMove && st.home.contains v && (← chance cfg.chaos.homeUse) then homeOf v
            else pure (.reg r)
        | .reg, _, some r => pure (.reg r)
        | .any, none, none =>
            if st.home.contains v then homeOf v
            else do
              let r ← grab (← targetRegOf v) (← isCrossCall v) (some v)
              addMove (.reg r) (← srcIn st v)
              pure (.reg r)
        | _, _, _ => do
            let hint := (← targetRegOf v).orElse fun _ => st.reg[v]?
            let r ← grab hint (← isCrossCall v) (some v)
            addMove (.reg r) (← srcIn st v)
            if (← liveAfter b i v) && !(← get).after.contains (some v) then
              modify fun p => { p with after := p.after.set! (ix r) (some v) }
            pure (.reg r)
      if let .reg r := loc then modify fun p => { p with needMid := p.needMid.set! (ix r) (some v) }
      useLoc := useLoc.insert v loc
      locs := locs.set! j (some loc)

    -- 4. Values that must leave their register (guided by IRC's color/spill decision).
    for (u, r) in relocate do
      let p ← get
      if p.after.contains (some u) then continue
      let targetU ← targetRegOf u
      let ok (q : X86.GPR) : Bool :=
        p.needMid[ix q]!.isNone && p.after[ix q]!.isNone && !p.blocked[ix q]! && !p.fixedReg[ix q]!
      -- If IRC spilled `u`, only spill immediately when `!mustReg` or `u` is already homed or no free reg survives.
      let wantSpill := targetU.isNone && !cfg.chaos.enabled &&
        (!(← mustRegOf u) || st.home.contains u || p.homeAfter.contains u || !clob.isEmpty)
      let dest ←
        if wantSpill || (← chance cfg.chaos.extraSpill) then pure none
        else pickReg ok targetU (!clob.isEmpty || (← isCrossCall u)) (some u)
      match dest with
      | some q =>
          addMove (.reg q) (.reg r)
          modify fun p => { p with needMid := p.needMid.set! (ix q) (some u), after := p.after.set! (ix q) (some u) }
      | none =>
          if !(st.home.contains u || (← get).homeAfter.contains u) then addMove (← homeOf u) (.reg r)
          modify fun p => { p with homeAfter := p.homeAfter.insert u }

    -- 5. Definitions (guided by IRC's coalesced target registers and spill slots).
    for (o, j) in ops.zipIdx do
      if o.kind != .define then continue
      let x := o.v
      let across ← isCrossCall x
      let hint ← targetRegOf x
      match o.con with
      | .fixed r =>
          modify fun p => { p with after := p.after.set! (ix r) (some x) }
      | .reuse k =>
          let a := opsA[k]!.v
          let aLive ← liveAfter b i a
          -- If `a` is live in `r` and `x` targets `r` while `a` has a different free IRC home `q`,
          -- move `a` to `q` now so `x` runs in place in `r` (e.g. `fib`: `mov rbx, rdi; sub rdi, 4`).
          if aLive then
            if let (some r, some h) := (st.reg[a]?, hint) then
              if r == h then
                let p ← get
                if !p.blocked[ix r]! && !p.fixedReg[ix r]! && p.after[ix r]! == some a &&
                    (p.needMid[ix r]!.isNone || p.needMid[ix r]! == some a) then
                  vacateToHome r false
          let p ← get
          let canInPlace := match st.reg[a]? with
            | some r =>
                if !p.blocked[ix r]! && !p.fixedReg[ix r]! && p.after[ix r]!.isNone &&
                    (p.needMid[ix r]!.isNone || p.needMid[ix r]! == some a) then some r else none
            | none => none
          -- Prefer moving to `hint` when `hint` is free and differs from `canInPlace` (so `x` lands
          -- in its IRC-coalesced color for downstream fixed uses / back-edges).
          let skipHint ← chance cfg.chaos.ignoreHint
          let inPlace := match canInPlace, hint with
            | some r, some h =>
                if r != h && p.needMid[ix h]!.isNone && p.after[ix h]!.isNone &&
                    !p.blocked[ix h]! && !p.fixedReg[ix h]! && !skipHint then
                  none
                else some r
            | ip, _ => ip
          let r ← match inPlace with
            | some r => pure r
            | none => do
                if let some h := hint then vacateToHome h true
                let r ← grab (hint.orElse fun _ => st.reg[a]?) across (some x)
                addMove (.reg r) (← srcIn st a)
                pure r
          modify fun p => { p with needMid := p.needMid.set! (ix r) (some a), after := p.after.set! (ix r) (some x) }
          locs := locs.set! k (some (.reg r))
          locs := locs.set! j (some (.reg r))
      | .reg | .any =>
          let srcCell := isMove && (locs[0]!.map Loc.isCell).getD false
          if o.pos == .early then
            if let some h := hint then vacateToHome h true
            let r ← grab hint across (some x)
            modify fun p => { p with after := p.after.set! (ix r) (some x) }
            locs := locs.set! j (some (.reg r))
          else if o.con == .any && !srcCell &&
              ((hint.isNone && !cfg.chaos.enabled && !(← mustRegOf x)) || (← chance cfg.chaos.homeDef)) then
            locs := locs.set! j (some (← homeOf x))
            modify fun p => { p with homeAfter := p.homeAfter.insert x }
          else if o.con == .any && !srcCell && hint.isNone && !cfg.chaos.enabled then
            -- `x` was spilled by IRC but has `.reg` uses: keep in a free register if one is open without eviction.
            let p ← get
            let okFree (r : X86.GPR) : Bool :=
              p.after[ix r]!.isNone && !p.blocked[ix r]! && !p.fixedReg[ix r]!
            match ← pickReg okFree none across (some x) with
            | some r =>
                modify fun p => { p with after := p.after.set! (ix r) (some x) }
                locs := locs.set! j (some (.reg r))
            | none =>
                locs := locs.set! j (some (← homeOf x))
                modify fun p => { p with homeAfter := p.homeAfter.insert x }
          else
            let effHint := if isMove && hint.isNone then st.reg[opsA[0]!.v]? else hint
            if let some h := effHint then vacateToHome h false
            match ← grabLate effHint across (effHint.isNone && !across) (some x) with
            | some r =>
                modify fun p => { p with after := p.after.set! (ix r) (some x) }
                locs := locs.set! j (some (.reg r))
            | none =>
                if o.con == .any && !srcCell then
                  locs := locs.set! j (some (← homeOf x))
                  modify fun p => { p with homeAfter := p.homeAfter.insert x }
                else throw s!"block {b} instruction {i}: no register for v{x}"
      | .stack => throw s!"block {b} instruction {i}: a stack definition (more than two results)"

    -- 6. A fixed use's register keeps its value afterwards when free.
    for r in scratch do
      let p ← get
      if let some v := p.fixedUse[ix r]! then
        if !p.blocked[ix r]! && p.after[ix r]!.isNone && !p.after.contains (some v) && (← liveAfter b i v) then
          modify fun p => { p with after := p.after.set! (ix r) (some v) }

    -- 7. Chaos perturbations.
    for r in scratch do
      let p ← get
      if let some u := p.after[ix r]! then
        if p.needMid[ix r]! == some u && p.st.get r == some u && !p.homeAfter.contains u &&
            (← chance cfg.chaos.spillAtDef) then
          addMove (← homeOf u) (.reg r)
          modify fun p => { p with homeAfter := p.homeAfter.insert u }
    if ← chance cfg.chaos.extraSpill then
      let _ ← evict fun _ => true

    let some ls := locs.toList.mapM id | throw s!"block {b} instruction {i}: an operand has no location"
    return ls

  let (ls, p) ← run.run plan
  let isDst (r : X86.GPR) : Bool := p.moves.any (·.1 == .reg r)
  let free := scratch.filter fun r => st.isFree r && p.needMid[ix r]!.isNone && !isDst r
  let (free, victim) ← chooseScratch free fun r => !st.isFree r
  let edits ← resolveMoves p.moves free victim
  modify fun s => { s with edits := s.edits.modify b fun es => es ++ edits.map ((i, ·)) }
  let mut occ : Array (Option VReg) := Array.replicate 16 none
  let mut reg : Std.HashMap VReg X86.GPR := {}
  for r in scratch do
    if let some v := p.after[ix r]! then
      if ← liveAfter b i v then
        occ := occ.set! (ix r) (some v)
        reg := reg.insert v r
  let mut home : Std.HashSet VReg := {}
  for v in p.homeAfter do
    if ← liveAfter b i v then home := home.insert v
  modify fun s => { s with cur := { occ, reg, home } }
  return ls

/-! ### Block boundaries -/

private def locsIn (s : RState) (v : VReg) : M (List Loc) := do
  let r := (s.reg[v]?).map Loc.reg |>.toList
  let h ← if s.home.contains v then pure [← homeOf v] else pure []
  return r ++ h

/-- Decide the entry state of block `s` reached from `fromBlock`.
- Multi-predecessor blocks (join blocks / loop headers) use IRC's global colors
  directly so hot back-edges have zero redundant copies — except that on an
  entry-block conditional header (`fromBlock == 0`, no calls in `s`), a
  parameter arriving in a caller-saved ABI register stays in that register when
  no other incoming edge's argument coalesces into its callee-saved IRC color
  (avoiding entry moves on 100% of recursive base-case calls, e.g. `tak`).
- Single-predecessor blocks inherit `X` lazily so cold/base-case paths avoid
  eager register shuffles. -/
private def decideEntry (fromBlock : Label) (s : Label) (X : RState) (args : List VReg) : M RState := do
  let cfg ← read
  let block := cfg.f.blocks[s]!
  let live := cfg.g.liveIn[s]!
  let unique := cfg.g.preds[s]!.length == 1
  let mut E : RState := {}
  if !unique then
    -- Check if `s` is an entry-block conditional header with no direct calls in `s`.
    let entryHeader := fromBlock == 0 && !cfg.chaos.enabled && block.term.edges.length ≥ 2 &&
      !block.body.any (fun | .call .. => true | _ => false)
    let mut keepAbiParam : Std.HashMap VReg X86.GPR := {}
    if entryHeader then
      for ((p, a), pIdx) in (block.params.zip args).zipIdx do
        if !live.contains p then continue
        if let (some rIn, some qIrc) := (X.reg[a]?, ← targetRegOf p) then
          if !calleeSavedRegs.contains rIn && calleeSavedRegs.contains qIrc then
            -- Check if any OTHER incoming edge into `s` arrives in `qIrc` for param `pIdx`.
            let mut otherUsesQ := false
            for pred in cfg.g.preds[s]! do
              if pred == fromBlock then continue
              for e' in cfg.f.blocks[pred]!.term.edges do
                if e'.target != s then continue
                if let some a' := e'.args[pIdx]? then
                  if (← targetRegOf a') == some qIrc then otherUsesQ := true
            if !otherUsesQ then
              keepAbiParam := keepAbiParam.insert p rIn
    -- Place non-ABI-kept live-ins in their IRC colors first, then ABI-kept params in `rIn` if free.
    let liveList := live.toList.toArray.qsort fun a b =>
      let wa := match cfg.g.vregToNode[a]? with | some u => cfg.g.weight[u]! | none => 0
      let wb := match cfg.g.vregToNode[b]? with | some u => cfg.g.weight[u]! | none => 0
      wa > wb || (wa == wb && a < b)
    for v in liveList do
      if keepAbiParam.contains v then continue
      let forceHome ← chance cfg.chaos.entryHome
      match ← targetRegOf v with
      | some r =>
          if !forceHome && E.isFree r then
            E := E.put v r
          else if !forceHome then
            match ← pickReg E.isFree (some r) (← isCrossCall v) (some v) with
            | some q => E := E.put v q
            | none => E := { E with home := E.home.insert v }
          else
            E := { E with home := E.home.insert v }
      | none =>
          E := { E with home := E.home.insert v }
    for v in liveList do
      let some rIn := keepAbiParam[v]? | continue
      if E.isFree rIn then
        E := E.put v rIn
      else
        match ← pickReg E.isFree (← targetRegOf v) (← isCrossCall v) (some v) with
        | some q => E := E.put v q
        | none => E := { E with home := E.home.insert v }
    return E
  else
    -- Single-predecessor block: inherit `X` lazily.
    let nonParams := (live.toList.filter fun v => !block.params.contains v).toArray.qsort fun a b =>
      let wa := match cfg.g.vregToNode[a]? with | some u => cfg.g.weight[u]! | none => 0
      let wb := match cfg.g.vregToNode[b]? with | some u => cfg.g.weight[u]! | none => 0
      wa > wb || (wa == wb && a < b)
    for v in nonParams do
      match X.reg[v]? with
      | some r =>
          if ← chance cfg.chaos.entryHome then E := { E with home := E.home.insert v }
          else E := E.put v r
      | none => E := { E with home := E.home.insert v }
      if X.home.contains v then E := { E with home := E.home.insert v }
    for (p, a) in block.params.zip args do
      if !live.contains p then continue
      let forceHome ← chance cfg.chaos.entryHome
      let hint ← targetRegOf p
      let cross ← isCrossCall p
      match X.reg[a]? with
      | some r =>
          if !forceHome && E.isFree r then
            E := E.put p r
          else if !forceHome then
            match ← pickReg E.isFree hint cross (some p) with
            | some q => E := E.put p q
            | none => E := { E with home := E.home.insert p }
          else
            E := { E with home := E.home.insert p }
      | none =>
          if forceHome || (hint.isNone && !cfg.chaos.enabled) then
            E := { E with home := E.home.insert p }
          else
            match ← pickReg E.isFree hint cross (some p) with
            | some q => E := E.put p q
            | none => E := { E with home := E.home.insert p }
    return E

private def edgeMoves (X E : RState) (params args : List VReg) : M (Array (Loc × Loc)) := do
  let argOf (v : VReg) : VReg := match (params.zip args).find? (·.1 == v) with
    | some (_, a) => a
    | none => v
  let mut moves : Array (Loc × Loc) := #[]
  for r in scratch do
    if let some v := E.get r then
      let src := argOf v
      if X.reg[src]? != some r then moves := moves.push (.reg r, ← srcIn X src)
  for v in E.home.toList do
    let src := argOf v
    if params.contains v then
      let h ← homeOf v
      if X.home.contains src && (← homeOf src) == h then
        pure ()
      else
        let s ← srcIn X src
        if s != h then moves := moves.push (h, s)
    else if !X.home.contains v then
      moves := moves.push (← homeOf v, ← srcIn X v)
  return moves

private def certFromExit (s : Label) (X : RState) (args : List VReg) : M (List (Loc × List VReg)) := do
  let cfg ← read
  let block := cfg.f.blocks[s]!
  let live := cfg.g.liveIn[s]!
  let mut facts : List (Loc × List VReg) := []
  for v in live.toList do
    if block.params.contains v then continue
    for l in ← locsIn X v do facts := (l, [v]) :: facts
  for (p, a) in block.params.zip args do
    if live.contains p then
      for l in ← locsIn X a do facts := (l, [p]) :: facts
  return facts

private def certOf (E : RState) : M (List (Loc × List VReg)) := do
  let mut facts : List (Loc × List VReg) := []
  for r in scratch do
    if let some v := E.get r then facts := (.reg r, [v]) :: facts
  for v in E.home.toList do facts := (← homeOf v, [v]) :: facts
  return facts

private def takeEdge (b : Label) (nEdges : Nat) (X : RState) (e : Edge VReg) : M Unit := do
  let cfg ← read
  let s := e.target
  let some block := cfg.f.blocks[s]? | throw s!"block {b}: edge to missing block {s}"
  let unique := cfg.g.preds[s]!.length == 1
  if !unique && nEdges != 1 then throw s!"block {b}: critical edge to block {s}"
  let live := cfg.g.liveIn[s]!
  let X := X.restrict fun v =>
    (live.contains v && !block.params.contains v) ||
      (block.params.zip e.args).any fun (p, a) => a == v && live.contains p
  let E ← match (← get).entry[s]! with
    | some E => pure E
    | none => do
        let E ← decideEntry b s X e.args
        let cert ← if unique then certFromExit s X e.args else certOf E
        modify fun st => { st with entry := st.entry.set! s (some E), certs := st.certs.set! s (some cert) }
        pure E
  let moves ← edgeMoves X E block.params e.args
  if moves.isEmpty then return
  let busy (r : X86.GPR) : Bool := !X.isFree r || !E.isFree r
  let free := scratch.filter (!busy ·)
  let (free, victim) ← chooseScratch free fun r => !X.isFree r
  let edits ← resolveMoves moves free victim
  if unique then
    modify fun st => { st with edits := st.edits.modify s fun es => edits.map ((0, ·)) ++ es }
  else
    let n := cfg.f.blocks[b]!.body.size
    modify fun st => { st with edits := st.edits.modify b fun es => es ++ edits.map ((n, ·)) }

private def allocBlock (b : Label) : M Unit := do
  let cfg ← read
  let block := cfg.f.blocks[b]!
  let some E := (← get).entry[b]! | throw s!"block {b} is not reached"
  modify fun s => { s with cur := E }
  let n := block.body.size
  let mut locs : Array (List Loc) := #[]
  for h : i in [:n] do
    let inst := block.body[i]
    let clob := match inst with
      | .call g .. => cfg.env.clobbers g
      | _ => []
    let isMove := match inst with | .move .. => true | _ => false
    locs := locs.push (← allocAt b i inst.operands clob isMove)
  let tl ← allocAt b n block.term.operands [] false
  modify fun s => { s with locs := s.locs.set! b locs, termLocs := s.termLocs.set! b tl }
  let X := (← get).cur
  let edges := block.term.edges
  for e in edges do takeEdge b edges.length X e

/-- Allocate function `f` using Chaitin-Briggs / Iterated Register Coalescing. -/
def run (env : Xl.Env) (f : Func VReg) (chaos : Chaos := {}) : Except String Output := do
  let g ← buildGraph env f
  let n := f.blocks.size
  let rng0 := mix64 (chaos.seed + 0x9c010a)
  let col := colorGraph g chaos rng0
  let order := if chaos.shuffle then
      (defaultOrder.zipIdx.toArray.qsort fun (a, i) (b, j) =>
        let ha := mix64 (rng0 + UInt64.ofNat (gprIndex a))
        let hb := mix64 (rng0 + UInt64.ofNat (gprIndex b))
        ha < hb || (ha == hb && i < j)).toList.map (·.1)
    else defaultOrder
  let cfg : MCfg := { f, g, col, env, chaos, order }

  -- Incoming stack parameters start with their `.inArg` homes; spill slots are materialized lazily via `slotRemap`.
  let mut homes : Std.HashMap VReg Loc := {}
  let mut E : RState := {}
  let mut cert : List (Loc × List VReg) := []
  for (p, i) in f.params.zipIdx do
    match Xl.paramLoc i with
    | .reg r =>
        if g.liveIn[0]!.contains p then E := E.put p r
    | l =>
        homes := homes.insert p l
        if g.liveIn[0]!.contains p then E := { E with home := E.home.insert p }
    cert := cert ++ [(Xl.paramLoc i, [p])]

  let st : MSt := {
    homes
    rng := rng0
    edits := Array.replicate n #[]
    locs := Array.replicate n #[]
    termLocs := Array.replicate n []
    certs := (Array.replicate n none).set! 0 (some cert)
    entry := (Array.replicate n none).set! 0 (some E)
  }
  let go : M Unit := do for b in g.order do allocBlock b
  let ((), st) ← (go.run cfg).run st
  let blocks := (List.range n).map fun b =>
    { locs := st.locs[b]!.toList, termLocs := st.termLocs[b]!, edits := st.edits[b]!.toList
      cert := mergeFacts ((st.certs[b]!).getD []) : BlockOut }
  return { blocks, numSlots := st.nextSlot }

end IxCC.Xv.Alloc.GraphColor
