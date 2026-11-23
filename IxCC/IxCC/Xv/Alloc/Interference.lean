import IxCC.Xv.Alloc.State

/-!
# Exact liveness and interference graph for graph-coloring allocation (untrusted)

Builds the dense, instruction-accurate interference graph and loop-weighted move
list for an Xv function, ready for Chaitin-Briggs / Iterated Register Coalescing
(`IxCC.Xv.Alloc.GraphColor`).

Everything here is untrusted producer code (`Xv.Validate.func` checks the final
`Alloc.Output`), total (fuel-bounded, zero `partial`), and uses dense node IDs:

- `0 .. 12`: the 13 precolored allocatable GPRs (`colorRegs`).
- `13 .. 13 + numVRegs - 1`: one node per virtual register occurring in `f`.

Precolored interferences are stored in a 13-bit bitmask (`preMask : Array UInt16`)
for O(1) checks during George/Briggs coalescing and color selection; virtual-virtual
interferences use sparse adjacency lists plus a `HashSet UInt64` edge table capped
by a compile-time work budget (`maxVRegs`, `maxEdges`).

**Call-result deferral.** A call result defined in a fixed register (`rax`/`rdx`)
that must survive a later clobber in the same block can remain in its fixed
register until that clobber (`deferOf`). While parked in `r_fix`, other live
values interfere with `r_fix` rather than with the result's post-call home color,
allowing values that die before the next call (such as `n` in `fib`) to share a
single callee-saved register with the call result. -/

namespace IxCC.Xv.Alloc.GraphColor

open IxCC.Lir (VReg Label Operand Kind Pos Con)

/-- Number of allocatable GPR colors (`scratch.length`). -/
def K : Nat := 13

/-- Compile-time node budget for graph coloring (falls back to linear scan above). -/
def maxVRegs : Nat := 2500

/-- Compile-time virtual-virtual interference edge budget. -/
def maxEdges : Nat := 150000

/-- Color index `0..12` to allocatable GPR: caller-saved (`0..8`, with RC-saved
`5..7`), then callee-saved (`9..12`). -/
def colorRegs : Array X86.GPR :=
  #[.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rbx, .r12, .r13, .r14]

/-- Allocatable GPR to color index `0..12`. Reserved registers return `none`. -/
def gprToColor : X86.GPR → Option Nat
  | .rax => some 0 | .rcx => some 1 | .rdx => some 2 | .rsi => some 3 | .rdi => some 4
  | .r8  => some 5 | .r9  => some 6 | .r10 => some 7 | .r11 => some 8
  | .rbx => some 9 | .r12 => some 10 | .r13 => some 11 | .r14 => some 12
  | .rsp | .rbp | .r15 => none

/-- Whether node ID `u` is a precolored GPR (`0..12`). -/
@[inline] def isPrecolored (u : Nat) : Bool := u < K

/-- Whether color index `c` is a callee-saved register (`rbx, r12, r13, r14`). -/
@[inline] def isCalleeSavedColor (c : Nat) : Bool := c ≥ 9 && c < K

/-- Single-color bit in a 13-bit mask. -/
@[inline] def colorBit (c : Nat) : UInt16 := (1 : UInt16) <<< UInt16.ofNat c

/-- Mask with all 13 allocatable color bits set. -/
def allColorsMask : UInt16 := 0x1FFF

/-- Bitmask for a list of GPRs (ignoring reserved registers). -/
def regsMask (rs : List X86.GPR) : UInt16 :=
  rs.foldl (fun m r => match gprToColor r with | some c => m ||| colorBit c | none => m) 0

/-- Population count of the low 13 bits of a `UInt16` mask. -/
def popcount13 (m : UInt16) : Nat := Id.run do
  let mut x := m &&& allColorsMask
  let mut c := 0
  for _ in [:K] do
    if (x &&& 1) != 0 then c := c + 1
    x := x >>> 1
  return c

/-- Canonical unordered edge key for two node IDs. -/
@[inline] def edgeKey (u v : Nat) : UInt64 :=
  let a := if u ≤ v then u else v
  let b := if u ≤ v then v else u
  (UInt64.ofNat a <<< 32) ||| UInt64.ofNat b

/-- Weighted move/affinity edge between two nodes (at most one precolored). -/
structure MoveEdge where
  u : Nat
  v : Nat
  weight : Nat
  deriving Repr, Inhabited

/-- A call result parked in its fixed register `color` across `(defPos, splitPos)`
of `block` before relocating to its home color at `splitPos`. -/
structure DeferInfo where
  block : Label
  defPos : Nat
  splitPos : Nat
  color : Nat
  deriving Repr, Inhabited

/-- Full analysis and interference graph for one function. -/
structure Graph where
  order : Array Label
  preds : Array (List Label)
  depth : Array Nat
  header : Array Bool
  liveIn : Array (Std.HashSet VReg)
  liveOut : Array (Std.HashSet VReg)
  uses : Array (Std.HashMap VReg (Array Nat))
  vregs : Array VReg
  vregToNode : Std.HashMap VReg Nat
  numNodes : Nat
  /-- Incoming stack parameter index (`i - 7`) for stack params, else `none`. -/
  inArgIdx : Array (Option Nat)
  /-- Precolored interference mask for each node. -/
  preMask : Array UInt16
  /-- Non-precolored interference adjacency lists (indexed by node ID). -/
  adjList : Array (Array Nat)
  /-- Exact virtual-virtual interference edge set (respecting call-result deferral). -/
  adjSet : Std.HashSet UInt64
  /-- Extra virtual-virtual interferences skipped due to deferral (for 100% sound spill-slot reuse). -/
  extraFullAdj : Std.HashSet UInt64
  /-- Loop-weighted spill cost for each node. -/
  weight : Array Nat
  /-- Whether node `u` has any register-requiring operand (`.reg`, `.fixed`, or `.reuse`-tied). -/
  mustReg : Array Bool
  /-- Whether node `u` is live across any call. -/
  crossCall : Array Bool
  /-- Bitmask of colors clobbered by calls node `u` is live across. -/
  callClobMask : Array UInt16
  /-- Non-interfering weighted move edges, sorted by descending weight. -/
  moves : Array MoveEdge
  /-- Call-result deferral info per node, if any. -/
  deferOf : Array (Option DeferInfo)
  deriving Inhabited

def Graph.hasVirtualEdge (g : Graph) (u v : Nat) : Bool :=
  g.adjSet.contains (edgeKey u v)

def Graph.interferes (g : Graph) (u v : Nat) : Bool :=
  if u == v then true
  else if isPrecolored u then
    if isPrecolored v then true
    else (g.preMask[v]! &&& colorBit u) != 0
  else if isPrecolored v then
    (g.preMask[u]! &&& colorBit v) != 0
  else
    g.adjSet.contains (edgeKey u v)

def Graph.interferesFull (g : Graph) (u v : Nat) : Bool :=
  if u == v then true
  else if isPrecolored u || isPrecolored v then g.interferes u v
  else
    let k := edgeKey u v
    g.adjSet.contains k || g.extraFullAdj.contains k

/-- Exact backward dataflow liveness (fuel-bounded, ignoring dead block params). -/
private def exactLiveness (f : Func VReg) (order : Array Label) :
    Except String (Array (Std.HashSet VReg) × Array (Std.HashSet VReg)) := do
  let n := f.blocks.size
  for h : b in [:n] do
    for e in f.blocks[b].term.edges do
      match f.blocks[e.target]? with
      | none => throw s!"block {b}: edge to missing block {e.target}"
      | some s =>
          if e.args.length != s.params.length then
            throw s!"block {b}: edge arity mismatch to block {e.target}"
  let mut liveIn : Array (Std.HashSet VReg) := Array.replicate n {}
  let mut liveOut : Array (Std.HashSet VReg) := Array.replicate n {}
  let post := order.reverse
  let mut changed := true
  for _ in [:n + 2] do
    if !changed then break
    changed := false
    for b in post do
      let block := f.blocks[b]!
      let mut out : Std.HashSet VReg := {}
      for e in block.term.edges do
        let s := f.blocks[e.target]!
        let sLive := liveIn[e.target]!
        for x in sLive do
          if !s.params.contains x then out := out.insert x
        for (p, a) in s.params.zip e.args do
          if sLive.contains p then out := out.insert a
      let top := liveTop block out
      if top.size != liveIn[b]!.size || out.size != liveOut[b]!.size then changed := true
      liveIn := liveIn.set! b top
      liveOut := liveOut.set! b out
  return (liveIn, liveOut)

/-- Loop-weighted move weight for an edge or instruction at loop depth `d`. -/
private def moveWeight (d : Nat) (base : Nat) : Nat :=
  base * (4 ^ (min d 8))

/-- Validate basic operand shapes that no allocation can satisfy, and collect all VRegs. -/
private def collectVRegs (f : Func VReg) : Except String (Array VReg × Std.HashMap VReg Nat) := do
  let mut vregs : Array VReg := #[]
  let mut map : Std.HashMap VReg Nat := {}
  let addV (vregs : Array VReg) (map : Std.HashMap VReg Nat) (v : VReg) :
      Array VReg × Std.HashMap VReg Nat :=
    if map.contains v then (vregs, map)
    else
      let id := K + vregs.size
      (vregs.push v, map.insert v id)
  for p in f.params do
    (vregs, map) := addV vregs map p
  for h : b in [:f.blocks.size] do
    let block := f.blocks[b]
    for p in block.params do
      (vregs, map) := addV vregs map p
    let nb := block.body.size
    for i in [:nb + 1] do
      let ops := opsAt block i
      let isCall := if h' : i < nb then
          match block.body[i] with | .call .. => true | _ => false
        else false
      let mut fixedSeen : Array (Option VReg) := Array.replicate 16 none
      for o in ops do
        (vregs, map) := addV vregs map o.v
        match o.con with
        | .stack =>
            if o.kind == .define then
              throw s!"block {b} instruction {i}: a stack definition (more than two results)"
            if !isCall then
              throw s!"block {b} instruction {i}: a stack operand outside call arguments"
        | .fixed r =>
            if Xl.reserved r then
              throw s!"block {b} instruction {i}: reserved fixed register {repr r}"
            if o.kind == .use then
              let ri := gprIndex r
              match fixedSeen[ri]! with
              | some w =>
                  if w != o.v then throw s!"block {b} instruction {i}: two values fixed to {repr r}"
              | none => fixedSeen := fixedSeen.set! ri (some o.v)
        | _ => pure ()
    for e in block.term.edges do
      for a in e.args do
        (vregs, map) := addV vregs map a
  if vregs.size > maxVRegs then
    throw s!"graph-coloring budget exceeded ({vregs.size} vregs > {maxVRegs})"
  return (vregs, map)

/-- Compute call-result deferral ranges (`deferOf`) and per-instruction parked
color lists (`parked[b][i]`). -/
private def computeDefers (f : Func VReg) (env : Xl.Env) (preds : Array (List Label))
    (liveIn : Array (Std.HashSet VReg)) (vregToNode : Std.HashMap VReg Nat)
    (numNodes : Nat) (callClobMask : Array UInt16) :
    Array (Option DeferInfo) × Array (Array (List (Nat × Nat))) := Id.run do
  let n := f.blocks.size
  let mut deferOf : Array (Option DeferInfo) := Array.replicate numNodes none
  let mut parked : Array (Array (List (Nat × Nat))) :=
    f.blocks.map fun blk => Array.replicate (blk.body.size + 1) []
  for b in [:n] do
    let block := f.blocks[b]!
    let nb := block.body.size
    for i in [:nb] do
      if let .call _ _ rets := block.body[i]! then
        for (x, idx) in rets.zipIdx do
          let some rFix := Lir.Conv.resultRegs[idx]? | continue
          let some cFix := gprToColor rFix | continue
          let some u := vregToNode[x]? | continue
          -- Only defer if `x` crosses a clobber of `rFix` (so it cannot stay in `rFix` forever).
          if (callClobMask[u]! &&& colorBit cFix) == 0 then continue
          -- Check whether every successor where `x` stays live has `b` as its sole predecessor.
          let canCrossTerm := block.term.edges.all fun e =>
            !(liveIn[e.target]!.contains x) || (preds[e.target]?.map (·.length)).getD 0 == 1
          -- Scan forward to find the earliest instruction where `rFix` is clobbered or fixed.
          let mut splitPos := i + 1
          for j in [i + 1 : nb + 1] do
            let clobbersRFix : Bool :=
              if h : j < nb then
                match block.body[j] with
                | .call g .. =>
                    (env.clobbers g).contains rFix ||
                      (block.body[j].operands).any fun o =>
                        match o.con with | .fixed r => r == rFix && (o.kind == .define || o.v != x) | _ => false
                | inst =>
                    inst.operands.any fun o =>
                      match o.con with | .fixed r => r == rFix && (o.kind == .define || o.v != x) | _ => false
              else
                !canCrossTerm ||
                  block.term.operands.any fun o =>
                    match o.con with | .fixed r => r == rFix && (o.kind == .define || o.v != x) | _ => false
            if clobbersRFix then
              splitPos := j
              break
            splitPos := j + 1
          -- `splitPos = nb + 1` means `x` stays parked in `rFix` through the terminator `nb` and
          -- enters its home color in single-predecessor successors (e.g. `fib`'s `brOvf` split).
          if splitPos > i + 1 then
            deferOf := deferOf.set! u (some { block := b, defPos := i, splitPos, color := cFix })
            let hi := min splitPos (nb + 1)
            for j in [i + 1 : hi] do
              parked := parked.modify b fun arr => arr.modify j fun ps => (u, cFix) :: ps
  return (deferOf, parked)

/-- Whether node `u` is using its home color (not parked in a fixed register) at `(b, pos)`. -/
@[inline] private def isHomeActive (deferOf : Array (Option DeferInfo)) (b pos u : Nat) : Bool :=
  match deferOf[u]! with
  | some d => !(d.block == b && d.defPos ≤ pos && pos < d.splitPos)
  | none => true

/-- Build the exact interference graph and weighted move list for `f`. -/
def buildGraph (env : Xl.Env) (f : Func VReg) : Except String Graph := do
  let n := f.blocks.size
  if n == 0 then throw "a function without blocks"
  let g := f.skeleton
  let order := g.rpo
  if order.size != n then throw "unreachable blocks"
  let preds := g.preds
  let (depth, header) := loopDepth f preds
  let (liveIn, liveOut) ← exactLiveness f order
  let (vregs, vregToNode) ← collectVRegs f
  let numNodes := K + vregs.size
  let uses := f.blocks.map usePositions

  -- Incoming stack params (`i ≥ 7`).
  let mut inArgIdx : Array (Option Nat) := Array.replicate numNodes none
  for (p, idx) in f.params.zipIdx do
    if idx ≥ Xl.nArgRegs then
      if let some u := vregToNode[p]? then
        inArgIdx := inArgIdx.set! u (some (idx - Xl.nArgRegs))

  -- Pre-pass: exact call clobbers & spill weights & `mustReg`.
  let mut crossCall : Array Bool := Array.replicate numNodes false
  let mut callClobMask : Array UInt16 := Array.replicate numNodes 0
  let mut weight : Array Nat := Array.replicate numNodes 0
  let mut mustReg : Array Bool := Array.replicate numNodes false

  for b in order do
    let block := f.blocks[b]!
    let nb := block.body.size
    let db := depth[b]!
    let mut live := liveOut[b]!
    for x in opDefs block.term.operands do live := live.erase x
    for x in opUses block.term.operands do live := live.insert x
    for k in [:nb] do
      let i := nb - 1 - k
      let ops := opsAt block i
      for x in opDefs ops do live := live.erase x
      if let .call gId .. := block.body[i]! then
        let mut cMask := regsMask (env.clobbers gId)
        for o in ops do
          if o.kind == .define then
            if let .fixed r := o.con then
              if let some c := gprToColor r then cMask := cMask ||| colorBit c
        for x in live do
          if let some u := vregToNode[x]? then
            crossCall := crossCall.set! u true
            let mut m := cMask
            for o in ops do
              if o.kind == .use && o.v != x then
                if let .fixed r := o.con then
                  if let some c := gprToColor r then m := m ||| colorBit c
            callClobMask := callClobMask.modify u (· ||| m)
      for x in opUses ops do live := live.insert x
    -- Operand weights (treat `.reuse`-tied uses as register-preferring, same as `.reg`).
    for i in [:nb + 1] do
      let ops := opsAt block i
      let tiedUses : List Nat := ops.filterMap fun o => match o.con with | .reuse k => some k | _ => none
      for (o, j) in ops.zipIdx do
        if let some u := vregToNode[o.v]? then
          let isTiedUse := o.kind == .use && tiedUses.contains j
          let effOp := if isTiedUse && o.con == .any then { o with con := .reg } else o
          let w := spillWeight db effOp
          weight := weight.modify u (· + w)
          match effOp.con with
          | .reg | .fixed _ => mustReg := mustReg.set! u true
          | _ => pure ()
    -- Block-parameter edge copy weights
    for e in block.term.edges do
      let s := f.blocks[e.target]!
      let ew := moveWeight (min db depth[e.target]!) 1000
      for (p, a) in s.params.zip e.args do
        if liveIn[e.target]!.contains p then
          if let some up := vregToNode[p]? then weight := weight.modify up (· + ew)
          if let some ua := vregToNode[a]? then weight := weight.modify ua (· + ew)

  -- Give register-required values a 2x weight boost over `.any`-only values (which fold into memory).
  for u in [K : numNodes] do
    let w := max 1 weight[u]!
    weight := weight.set! u (if mustReg[u]! then w * 2 else w)

  -- Call-result deferral ranges.
  let (deferOf, parked) := computeDefers f env preds liveIn vregToNode numNodes callClobMask

  -- Build interference graph and move map.
  let mut preMask : Array UInt16 := Array.replicate numNodes 0
  for c in [:K] do
    preMask := preMask.set! c (allColorsMask ^^^ colorBit c)
  let mut adjList : Array (Array Nat) := Array.replicate numNodes #[]
  let mut adjSet : Std.HashSet UInt64 := {}
  let mut extraFullAdj : Std.HashSet UInt64 := {}
  let mut moveWeights : Std.HashMap UInt64 Nat := {}

  let addPre (preMask : Array UInt16) (u c : Nat) : Array UInt16 :=
    if u ≥ K && c < K then preMask.modify u (· ||| colorBit c) else preMask

  let addPreMask (preMask : Array UInt16) (u : Nat) (m : UInt16) : Array UInt16 :=
    if u ≥ K then preMask.modify u (· ||| m) else preMask

  let addExtraFull (ef : Std.HashSet UInt64) (adjSet : Std.HashSet UInt64) (u v : Nat) : Std.HashSet UInt64 :=
    if u == v || u < K || v < K then ef
    else
      let k := edgeKey u v
      if adjSet.contains k then ef else ef.insert k

  let addVEdge (adjList : Array (Array Nat)) (adjSet : Std.HashSet UInt64) (u v : Nat) :
      Array (Array Nat) × Std.HashSet UInt64 :=
    if u == v || u < K || v < K then (adjList, adjSet)
    else
      let k := edgeKey u v
      if adjSet.contains k then (adjList, adjSet)
      else
        let adjList := (adjList.modify u (·.push v)).modify v (·.push u)
        (adjList, adjSet.insert k)

  let addClique (adjList : Array (Array Nat)) (adjSet : Std.HashSet UInt64) (nodes : Array Nat) :
      Except String (Array (Array Nat) × Std.HashSet UInt64) := do
    let mut al := adjList
    let mut as := adjSet
    let m := nodes.size
    for i in [:m] do
      let u := nodes[i]!
      for j in [i + 1 : m] do
        let v := nodes[j]!
        (al, as) := addVEdge al as u v
      if as.size > maxEdges then
        throw s!"graph-coloring edge budget exceeded ({as.size} > {maxEdges})"
    return (al, as)

  let addMove (mw : Std.HashMap UInt64 Nat) (u v w : Nat) : Std.HashMap UInt64 Nat :=
    if u == v || (isPrecolored u && isPrecolored v) then mw
    else
      let k := edgeKey u v
      mw.insert k (mw.getD k 0 + w)

  -- Entry parameter move preferences & entry clique.
  for (p, idx) in f.params.zipIdx do
    if idx < Xl.nArgRegs && liveIn[0]!.contains p then
      if let some r := Lir.Conv.argRegs[idx]? then
        if let some c := gprToColor r then
          if let some u := vregToNode[p]? then
            moveWeights := addMove moveWeights u c 1200

  -- Per-block interferences & moves.
  for b in order do
    let block := f.blocks[b]!
    let nb := block.body.size
    let db := depth[b]!

    -- 1. Entry live-in clique (guarantees distinct locations at block entry).
    let mut inNodes : Array Nat := #[]
    for x in liveIn[b]! do
      if let some u := vregToNode[x]? then inNodes := inNodes.push u
    (adjList, adjSet) ← addClique adjList adjSet inNodes

    -- 2. Exit live-out clique & block-param edge moves.
    let blockHasDefer := parked[b]!.any (!·.isEmpty)
    let mut outNodes : Array Nat := #[]
    let mut deferredOut : Array Nat := #[]
    for x in liveOut[b]! do
      if let some u := vregToNode[x]? then
        if isHomeActive deferOf b nb u then outNodes := outNodes.push u
        else deferredOut := deferredOut.push u
    (adjList, adjSet) ← addClique adjList adjSet outNodes
    if !deferredOut.isEmpty then
      for du in deferredOut do
        for ou in outNodes do
          extraFullAdj := addExtraFull extraFullAdj adjSet du ou
        for du2 in deferredOut do
          extraFullAdj := addExtraFull extraFullAdj adjSet du du2

    for e in block.term.edges do
      let s := f.blocks[e.target]!
      let sLive := liveIn[e.target]!
      -- Hot back-edges have higher `min db depth[e.target]` than cold preheaders.
      let ew := moveWeight (min db depth[e.target]!) 1500
      for (p, a) in s.params.zip e.args do
        if sLive.contains p then
          if let (some up, some ua) := (vregToNode[p]?, vregToNode[a]?) then
            moveWeights := addMove moveWeights up ua ew

    -- 3. Backward instruction walk using dense node IDs in `live`.
    let mut live : Std.HashSet Nat := {}
    for x in liveOut[b]! do
      if let some u := vregToNode[x]? then live := live.insert u
    for k in [:nb + 1] do
      let i := nb - k
      let ops := opsAt block i
      let opsA := ops.toArray
      let clobMask : UInt16 :=
        if h : i < nb then
          match block.body[i] with
          | .call gId .. => regsMask (env.clobbers gId)
          | _ => 0
        else 0
      let isMoveInst : Bool :=
        if h : i < nb then
          match block.body[i] with | .move .. => true | _ => false
        else false

      -- Separate uses and defs as node IDs.
      let mut defNodes : Array (Operand VReg × Nat) := #[]
      let mut useNodes : Array (Operand VReg × Nat) := #[]
      for o in ops do
        if let some u := vregToNode[o.v]? then
          if o.kind == .define then defNodes := defNodes.push (o, u)
          else useNodes := useNodes.push (o, u)

      let isDefNode (u : Nat) : Bool := defNodes.any fun (_, ud) => ud == u

      -- Collect active live-after nodes and live-across nodes (`activeAfter \ defs`).
      let mut activeAfter : Array Nat := #[]
      let mut liveAcross : Array Nat := #[]
      let mut deferredAfter : Array Nat := #[]
      for u in live do
        if !blockHasDefer || isHomeActive deferOf b i u then
          activeAfter := activeAfter.push u
          if !isDefNode u then liveAcross := liveAcross.push u
        else
          deferredAfter := deferredAfter.push u

      -- Call clobbers apply to values live ACROSS the call (not the call's own results!).
      if clobMask != 0 then
        for u in liveAcross do
          preMask := addPreMask preMask u clobMask

      -- Defs interfere with each other and with all `activeAfter` (including `src` of `.move` if live!).
      for di in [:defNodes.size] do
        let (od, ud) := defNodes[di]!
        let activeD := !blockHasDefer || isHomeActive deferOf b i ud
        if blockHasDefer then
          for dj in [di + 1 : defNodes.size] do
            let (_, ud2) := defNodes[dj]!
            if !activeD || !isHomeActive deferOf b i ud2 then
              extraFullAdj := addExtraFull extraFullAdj adjSet ud ud2
          for ua in deferredAfter do
            if ua != ud then extraFullAdj := addExtraFull extraFullAdj adjSet ud ua
          if !activeD then
            for ua in activeAfter do
              if ua != ud then extraFullAdj := addExtraFull extraFullAdj adjSet ud ua
          if od.pos == .early then
            for (_, uu) in useNodes do
              if uu != ud && (!activeD || !isHomeActive deferOf b i uu) then
                extraFullAdj := addExtraFull extraFullAdj adjSet ud uu
        if activeD then
          for dj in [di + 1 : defNodes.size] do
            let (_, ud2) := defNodes[dj]!
            if !blockHasDefer || isHomeActive deferOf b i ud2 then
              (adjList, adjSet) := addVEdge adjList adjSet ud ud2
          for ua in activeAfter do
            if ua != ud then
              (adjList, adjSet) := addVEdge adjList adjSet ud ua
          -- Early def interferes with all uses.
          if od.pos == .early then
            for (_, uu) in useNodes do
              if uu != ud && (!blockHasDefer || isHomeActive deferOf b i uu) then
                (adjList, adjSet) := addVEdge adjList adjSet ud uu
        -- Fixed def: interferes with `activeAfter \ {ud}` and adds high-priority preference `(ud, c)`.
        if let .fixed r := od.con then
          if let some c := gprToColor r then
            for ua in activeAfter do
              if ua != ud then preMask := addPre preMask ua c
            if activeD then
              moveWeights := addMove moveWeights ud c (moveWeight db 2800)
        -- Tied `.reuse idx` def: move edge `(ud, tiedUse)` when tiedUse dies.
        if let .reuse idx := od.con then
          if let some uo := opsA[idx]? then
            if let some uu := vregToNode[uo.v]? then
              if !live.contains uu && activeD && (!blockHasDefer || isHomeActive deferOf b i uu) then
                moveWeights := addMove moveWeights ud uu (moveWeight db 2500)

      -- `.move dst src` when `src` dies here: coalesce `dst` and `src`.
      if isMoveInst then
        match useNodes[0]?, defNodes[0]? with
        | some (_, uu), some (_, ud) =>
            if !live.contains uu && (!blockHasDefer || (isHomeActive deferOf b i ud && isHomeActive deferOf b i uu)) then
              moveWeights := addMove moveWeights ud uu (moveWeight db 2200)
        | _, _ => pure ()

      -- Late uses interfere with all defs; fixed uses add high-priority preference and block other operands/survivors.
      for (ou, uu) in useNodes do
        let activeU := !blockHasDefer || isHomeActive deferOf b i uu
        if ou.pos == .late then
          for (_, ud) in defNodes do
            if ud != uu then
              if activeU && (!blockHasDefer || isHomeActive deferOf b i ud) then
                (adjList, adjSet) := addVEdge adjList adjSet uu ud
              else
                extraFullAdj := addExtraFull extraFullAdj adjSet uu ud
        if let .fixed r := ou.con then
          if let some c := gprToColor r then
            if activeU then
              moveWeights := addMove moveWeights uu c (moveWeight db 2800)
            for ua in liveAcross do
              if ua != uu then preMask := addPre preMask ua c
            for (_, uu2) in useNodes do
              if uu2 != uu && (!blockHasDefer || isHomeActive deferOf b i uu2) then
                preMask := addPre preMask uu2 c
            for (od, ud) in defNodes do
              if od.pos == .early && ud != uu && (!blockHasDefer || isHomeActive deferOf b i ud) then
                preMask := addPre preMask ud c

      -- Parked deferred values at `(b, i)` occupy their `cFix`.
      if blockHasDefer then
        for (ux, cFix) in parked[b]![i]! do
          for (_, ud) in defNodes do
            if ud != ux && isHomeActive deferOf b i ud then
              preMask := addPre preMask ud cFix
          for (_, uu) in useNodes do
            if uu != ux && isHomeActive deferOf b i uu then
              preMask := addPre preMask uu cFix
          for ua in activeAfter do
            if ua != ux then
              preMask := addPre preMask ua cFix

      if adjSet.size > maxEdges then
        throw s!"graph-coloring edge budget exceeded ({adjSet.size} > {maxEdges})"

      -- Update `live` to `liveBefore(i)`.
      for (_, ud) in defNodes do live := live.erase ud
      for (_, uu) in useNodes do live := live.insert uu

      -- Any deferred node whose `splitPos == i` transitions into its home color right before `i`:
      -- it interferes with everything home-active in `liveBefore(i)`.
      if blockHasDefer && i > 0 then
        for (ux, _) in parked[b]![i - 1]! do
          if let some d := deferOf[ux]! then
            if d.splitPos == i then
              for u in live do
                if u != ux && isHomeActive deferOf b i u then
                  (adjList, adjSet) := addVEdge adjList adjSet ux u

  -- Filter out moves whose endpoints already interfere, and sort descending by weight.
  let mut moves : Array MoveEdge := #[]
  for (k, w) in moveWeights.toList do
    let u := (k >>> 32).toNat
    let v := (k &&& 0xFFFFFFFF).toNat
    let interferesAlready :=
      if isPrecolored u then (preMask[v]! &&& colorBit u) != 0
      else if isPrecolored v then (preMask[u]! &&& colorBit v) != 0
      else adjSet.contains (edgeKey u v)
    if !interferesAlready then
      moves := moves.push { u, v, weight := w }
  moves := moves.qsort fun a b =>
    a.weight > b.weight || (a.weight == b.weight && (a.u < b.u || (a.u == b.u && a.v < b.v)))

  return {
    order, preds, depth, header, liveIn, liveOut, uses,
    vregs, vregToNode, numNodes, inArgIdx,
    preMask, adjList, adjSet, extraFullAdj, weight, mustReg, crossCall, callClobMask, moves, deferOf
  }

end IxCC.Xv.Alloc.GraphColor
