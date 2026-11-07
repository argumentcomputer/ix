import IxCC.Xv.Alloc.State

/-!
# SSA linear scan (untrusted)

The allocator of 05 §5, as a single forward scan over the blocks in reverse
postorder (the "second-chance binpacking" form of linear scan). Each live
register sits in at most one machine register and possibly its home cell;
the scan keeps values in registers as long as it can and splits their
lifetimes where it must:

- **before uses**: a `reg` use of a value that is only in its home reloads
  it (and the value stays in that register afterwards, so later uses do
  not reload again: redundant-reload elimination); `any` uses read the home
  directly;
- **at conflicts**: a value whose register an instruction needs (a fixed
  operand, a call's clobber set, a fixed definition) moves to a free
  register (callee-saved across calls) or to its home, and a register
  demand with none free evicts the value with the least spill weight per
  distance to its next use (weights `1000·4^depth` plus bonuses, as in
  regalloc2);
- **at block boundaries**: the first predecessor to reach a block fixes
  its entry locations (keeping the predecessor's registers, and giving
  block parameters their arguments' registers where free); every other
  edge reconciles with a parallel move (`ParMove.resolve`), at the target's
  head when it has one predecessor and at the source's tail otherwise.

**Hints**: a tie reuses its dying operand's register, unless its result is
bound for a free fixed register (a dividend for `rax`), which it takes with
the copy its fixed use would need anyway; a definition prefers the register
of its first fixed use (unless it lives across a call, which prefers
callee-saved registers), and when a value occupying that register must leave
it before the next call anyway, it moves to a callee-saved register now
(`vacate`); a value flowing into a block parameter prefers that parameter's
register once the target's entry is fixed.

**Operand placement** per instruction: the moves before it form one
parallel move (reads, then writes), after which every use's register holds
it; definitions take registers that no surviving value needs, a late
definition possibly the register of a use that dies here, an early one
never a use's.

The output is an `Alloc.Output`: the certificate the validator checks. A
`Chaos` configuration perturbs register order, hints, spill choice, split
points and the move scratch (05 §12 item 3).
-/

namespace IxCC.Xv.Alloc.LinearScan

open IxCC.Lir (VReg Label FunId Operand Kind Pos Con)

structure Cfg where
  f : Func VReg
  info : Info
  env : Xl.Env
  chaos : Chaos
  order : List X86.GPR
  uses : Array (Std.HashMap VReg (Array Nat))

structure St where
  homes : Std.HashMap VReg Loc := {}
  nextSlot : Nat := 0
  cycleSlot : Option Nat := none
  saveSlot : Option Nat := none
  rng : UInt64
  edits : Array (Array (Nat × Edit))
  locs : Array (Array (List Loc))
  termLocs : Array (List Loc)
  certs : Array (Option (List (Loc × List VReg)))
  entry : Array (Option RState)
  hints : Std.HashMap VReg X86.GPR := {}
  cur : RState := {}

abbrev M := ReaderT Cfg (StateT St (Except String))

def rand : M UInt64 :=
  modifyGet fun s => let t := s.rng + 0x9e3779b97f4a7c15; (mix64 t, { s with rng := t })

def chance (p : Nat) : M Bool := do
  if p == 0 then return false
  return (← rand).toNat % 100 < p

def pickOne {α : Type} [Inhabited α] (xs : List α) : M α := do
  return xs[(← rand).toNat % xs.length]!

def homeOf (v : VReg) : M Loc := do
  match (← get).homes[v]? with
  | some l => pure l
  | none =>
      modifyGet fun s =>
        (.slot s.nextSlot, { s with homes := s.homes.insert v (.slot s.nextSlot), nextSlot := s.nextSlot + 1 })

def srcIn (s : RState) (v : VReg) : M Loc :=
  match s.reg[v]? with
  | some r => pure (.reg r)
  | none => if s.home.contains v then homeOf v else throw s!"v{v} has no location"

/-- Whether `v` is live after instruction `i` of block `b`. -/
def liveAfter (b : Label) (i : Nat) (v : VReg) : M Bool := do
  let cfg ← read
  if cfg.info.liveOut[b]!.contains v then return true
  match cfg.uses[b]![v]? with
  | some ps => return ps.any (· > i)
  | none => return false

/-- Instructions to `v`'s next use in block `b` after `i` (far when none). -/
def nextUse (b : Label) (i : Nat) (v : VReg) : M Nat := do
  let cfg ← read
  let n := cfg.f.blocks[b]!.body.size
  match (cfg.uses[b]![v]?).bind (·.find? (· > i)) with
  | some j => return j - i
  | none => return n + 1 - i + 64

def weightOf (v : VReg) : M Nat := do return (← read).info.weight.getD v 1

/-- A register preference order: callee-saved first for values live across
calls. -/
def orderFor (acrossCall : Bool) : M (List X86.GPR) := do
  let o := (← read).order
  if acrossCall then
    return o.filter calleeSavedRegs.contains ++ o.filter (!calleeSavedRegs.contains ·)
  return o

/-- The first register satisfying `ok`: the hint if it does (unless chaos
ignores it), then the first `regLimit` of the order, then any. -/
def pickReg (ok : X86.GPR → Bool) (hint : Option X86.GPR) (acrossCall : Bool) : M (Option X86.GPR) := do
  let cfg ← read
  if let some h := hint then
    if ok h && !(← chance cfg.chaos.ignoreHint) then return some h
  let base ← orderFor acrossCall
  match (base.take cfg.chaos.regLimit).find? ok with
  | some r => return some r
  | none => return base.find? ok

/-- Free registers for a parallel move's scratch, and the victim to borrow
when none is: a register holding a value (saving an empty register would
read an undefined location, which Xl rejects). Chaos may withhold the free
registers to exercise the extra slot and the victim. -/
def chooseScratch (free : List X86.GPR) (holding : X86.GPR → Bool) : M (List X86.GPR × X86.GPR) := do
  let cfg ← read
  let victims := scratch.filter fun r => holding r && !free.contains r
  let free := if !victims.isEmpty && (← chance cfg.chaos.noFreeScratch) then [] else free
  let victim ← match victims with
    | [] => pure (free.headD .r11)
    | v :: _ => if cfg.chaos.randomVictim > 0 then pickOne victims else pure v
  return (free, victim)

/-! ## One instruction -/

structure Plan where
  b : Label
  i : Nat
  st : RState
  usedHere : Std.HashSet VReg
  /-- What each register holds while the instruction runs. -/
  needMid : Array (Option VReg) := Array.replicate 16 none
  /-- What each register holds after it. -/
  after : Array (Option VReg) := Array.replicate 16 none
  homeAfter : Std.HashSet VReg
  moves : Array (Loc × Loc) := #[]
  /-- Clobbered or written by a fixed definition: nothing survives there. -/
  blocked : Array Bool := Array.replicate 16 false
  /-- A fixed operand's register. -/
  fixedReg : Array Bool := Array.replicate 16 false
  fixedUse : Array (Option VReg) := Array.replicate 16 none

abbrev P := StateT Plan M

def ix (r : X86.GPR) : Nat := gprIndex r

def addMove (dst src : Loc) : P Unit :=
  if dst == src then pure () else modify fun p => { p with moves := p.moves.push (dst, src) }

/-- Evict a surviving value that this instruction does not use, making its
register free for the instruction. -/
def evict (ok : X86.GPR → Bool) : P (Option X86.GPR) := do
  let p ← get
  let mut cands : Array (X86.GPR × VReg) := #[]
  for r in scratch do
    match p.after[ix r]!, p.needMid[ix r]! with
    | some u, some u' =>
        -- Only a value already in `r` before the instruction: one this plan
        -- moves into `r` has its move's source elsewhere.
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
      let key := (w * 1024) / (d + 1) * 2 + (if homed then 0 else 1)
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

/-- A register free for the instruction (nothing needs it during or after),
or an evicted one. -/
def grab (hint : Option X86.GPR) (acrossCall : Bool) : P X86.GPR := do
  let p ← get
  let ok (r : X86.GPR) : Bool :=
    p.needMid[ix r]!.isNone && p.after[ix r]!.isNone && !p.blocked[ix r]! && !p.fixedReg[ix r]!
  match ← pickReg ok hint acrossCall with
  | some r => return r
  | none =>
      match ← evict fun _ => true with
      | some r => return r
      | none => throw s!"block {p.b} instruction {p.i}: no register is free"

/-- A register for a late definition: free after the instruction, possibly
holding a use that dies here. -/
def grabLate (hint : Option X86.GPR) (acrossCall : Bool) (preferDying : Bool) : P (Option X86.GPR) := do
  let p ← get
  let ok (r : X86.GPR) : Bool := p.after[ix r]!.isNone && !p.blocked[ix r]! && !p.fixedReg[ix r]!
  let dying := scratch.filter fun r => ok r && p.needMid[ix r]!.isSome
  if preferDying && hint.isNone then
    if let some r := dying.head? then return some r
  match ← pickReg ok hint acrossCall with
  | some r => return some r
  | none => evict fun _ => true

/-- Whether a call later in block `b` clobbers `r` while `u` is live across
it: then `u` must leave `r` before that call anyway. -/
def leavesBeforeCall (b : Label) (i : Nat) (u : VReg) (r : X86.GPR) : M Bool := do
  let cfg ← read
  let body := cfg.f.blocks[b]!.body
  for c in [i + 1:body.size] do
    if let .call g .. := body[c]! then
      if (cfg.env.clobbers g).contains r then return ← liveAfter b c u
  return false

/-- Give a definition its hinted register `h` when the value there would
have to leave before the next call anyway: move it now to a free
callee-saved register, which costs the same move and saves a copy into `h`
later. -/
def vacate (h : X86.GPR) : P Unit := do
  let p ← get
  let some u := p.after[ix h]! | return
  unless p.st.get h == some u && !p.blocked[ix h]! && !p.fixedReg[ix h]! do return
  unless ← leavesBeforeCall p.b p.i u h do return
  let ok (q : X86.GPR) : Bool :=
    p.needMid[ix q]!.isNone && p.after[ix q]!.isNone && !p.blocked[ix q]! && !p.fixedReg[ix q]! &&
      calleeSavedRegs.contains q
  if let some q ← pickReg ok none true then
    addMove (.reg q) (.reg h)
    modify fun p =>
      { p with needMid := p.needMid.set! (ix q) (some u), after := (p.after.set! (ix q) (some u)).set! (ix h) none }

def hintFor (v : VReg) : M (Option X86.GPR) := do
  let cfg ← read
  if let some r := (← get).hints[v]? then return some r
  if cfg.info.crossCall.contains v then return none
  return cfg.info.fixedHint[v]?

/-- Allocate one instruction (or terminator) with operands `ops` and
clobbered registers `clob`; returns the operands' locations and leaves the
new state in `cur` and the moves before it in the block's edits. -/
def allocAt (b : Label) (i : Nat) (ops : List (Operand VReg)) (clob : List X86.GPR) (isMove : Bool) :
    M (List Loc) := do
  let cfg ← read
  let st := (← get).cur
  let opsA := ops.toArray
  let usedHere : Std.HashSet VReg := (opUses ops).foldl (·.insert ·) {}
  let tied : List Nat := ops.filterMap fun o => match o.con with | .reuse k => some k | _ => none
  let plan : Plan := { b, i, st, usedHere, homeAfter := st.home }
  let run : P (List Loc) := do
    let mut locs : Array (Option Loc) := Array.replicate ops.length none
    for r in clob do modify fun p => { p with blocked := p.blocked.set! (ix r) true }
    -- Fixed and convention operands.
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
    -- Surviving values stay unless their register is needed.
    let mut relocate : Array (VReg × X86.GPR) := #[]
    for r in scratch do
      if let some u := st.get r then
        let p ← get
        let readable := p.fixedUse[ix r]!.isNone || p.fixedUse[ix r]! == some u
        if ← liveAfter b i u then
          if !p.blocked[ix r]! && readable then
            set { p with needMid := p.needMid.set! (ix r) (some u), after := p.after.set! (ix r) (some u) }
          else relocate := relocate.push (u, r)
        -- A value this instruction reads keeps its register until it has read it.
        if readable && usedHere.contains u then
          modify fun p => { p with needMid := p.needMid.set! (ix r) (some u) }
    -- Other uses: `reg` first, then `any`; tied uses go with their definitions.
    let mut useLoc : Std.HashMap VReg Loc := {}
    let order := (ops.zipIdx.filter fun (o, j) =>
        o.kind == .use && !tied.contains j && (o.con == .reg || o.con == .any))
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
              let r ← grab none false
              addMove (.reg r) (← srcIn st v)
              pure (.reg r)
        | _, _, _ => do
            let r ← grab ((← get).st.reg[v]?) false
            addMove (.reg r) (← srcIn st v)
            if (← liveAfter b i v) && !(← get).after.contains (some v) then
              modify fun p => { p with after := p.after.set! (ix r) (some v) }
            pure (.reg r)
      if let .reg r := loc then modify fun p => { p with needMid := p.needMid.set! (ix r) (some v) }
      useLoc := useLoc.insert v loc
      locs := locs.set! j (some loc)
    -- Values that must leave their register.
    for (u, r) in relocate do
      let p ← get
      if p.after.contains (some u) then continue
      let ok (q : X86.GPR) : Bool :=
        p.needMid[ix q]!.isNone && p.after[ix q]!.isNone && !p.blocked[ix q]! && !p.fixedReg[ix q]!
      let dest ← if ← chance cfg.chaos.extraSpill then pure none
        else pickReg ok (← hintFor u) (!clob.isEmpty || cfg.info.crossCall.contains u)
      match dest with
      | some q =>
          addMove (.reg q) (.reg r)
          modify fun p => { p with needMid := p.needMid.set! (ix q) (some u), after := p.after.set! (ix q) (some u) }
      | none =>
          if !(st.home.contains u || (← get).homeAfter.contains u) then addMove (← homeOf u) (.reg r)
          modify fun p => { p with homeAfter := p.homeAfter.insert u }
    -- Definitions.
    for (o, j) in ops.zipIdx do
      if o.kind != .define then continue
      let x := o.v
      let across := cfg.info.crossCall.contains x
      match o.con with
      | .fixed r => modify fun p => { p with after := p.after.set! (ix r) (some x) }
      | .reuse k =>
          let a := opsA[k]!.v
          let p ← get
          let inPlace := match st.reg[a]? with
            | some r =>
                if !p.blocked[ix r]! && !p.fixedReg[ix r]! && p.after[ix r]!.isNone &&
                    (p.needMid[ix r]!.isNone || p.needMid[ix r]! == some a) then some r else none
            | none => none
          let inPlace ← match inPlace with
            | some r => if ← liveAfter b i a then pure none else pure (some r)
            | none => pure none
          -- A definition bound for a fixed register (a dividend for `rax`)
          -- goes there now if it is free: the copy it costs replaces the
          -- one its fixed use would need.
          let fixedHint := if cfg.info.crossCall.contains x then none else cfg.info.fixedHint[x]?
          let inPlace := match inPlace, fixedHint with
            | some r, some h =>
                let p' := p
                if r != h && p'.needMid[ix h]!.isNone && p'.after[ix h]!.isNone && !p'.blocked[ix h]! &&
                    !p'.fixedReg[ix h]! then none else some r
            | ip, _ => ip
          let r ← match inPlace with
            | some r => pure r
            | none => do
                let r ← grab ((← hintFor x).orElse fun _ => st.reg[a]?) across
                addMove (.reg r) (← srcIn st a)
                pure r
          modify fun p => { p with needMid := p.needMid.set! (ix r) (some a), after := p.after.set! (ix r) (some x) }
          locs := locs.set! k (some (.reg r))
          locs := locs.set! j (some (.reg r))
      | .reg | .any =>
          let srcCell := isMove && (locs[0]!.map Loc.isCell).getD false
          if o.pos == .early then
            let r ← grab (← hintFor x) across
            modify fun p => { p with after := p.after.set! (ix r) (some x) }
            locs := locs.set! j (some (.reg r))
          else if o.con == .any && !srcCell && (← chance cfg.chaos.homeDef) then
            locs := locs.set! j (some (← homeOf x))
            modify fun p => { p with homeAfter := p.homeAfter.insert x }
          else
            let hint ← hintFor x
            let hint := if isMove && hint.isNone then st.reg[opsA[0]!.v]? else hint
            if let some h := hint then vacate h
            match ← grabLate hint across (hint.isNone && !across) with
            | some r =>
                modify fun p => { p with after := p.after.set! (ix r) (some x) }
                locs := locs.set! j (some (.reg r))
            | none =>
                if o.con == .any && !srcCell then
                  locs := locs.set! j (some (← homeOf x))
                  modify fun p => { p with homeAfter := p.homeAfter.insert x }
                else throw s!"block {b} instruction {i}: no register for v{x}"
      | .stack => throw s!"block {b} instruction {i}: a stack definition (more than two results)"
    -- A fixed use's register keeps the value afterwards when nothing else needs it.
    for r in scratch do
      let p ← get
      if let some v := p.fixedUse[ix r]! then
        if !p.blocked[ix r]! && p.after[ix r]!.isNone && !p.after.contains (some v) && (← liveAfter b i v) then
          modify fun p => { p with after := p.after.set! (ix r) (some v) }
    -- Chaos: store survivors early, or evict one (a split before this point).
    for r in scratch do
      let p ← get
      if let some u := p.after[ix r]! then
        if p.needMid[ix r]! == some u && p.st.get r == some u && !p.homeAfter.contains u && (← chance cfg.chaos.spillAtDef) then
          addMove (← homeOf u) (.reg r)
          modify fun p => { p with homeAfter := p.homeAfter.insert u }
    if ← chance cfg.chaos.extraSpill then
      let _ ← evict fun _ => true
    let some ls := locs.toList.mapM id | throw s!"block {b} instruction {i}: an operand has no location"
    return ls
  let (ls, p) ← run.run plan
  -- Resolve the moves before the instruction.
  let isDst (r : X86.GPR) : Bool := p.moves.any (·.1 == .reg r)
  let free := scratch.filter fun r => st.isFree r && p.needMid[ix r]!.isNone && !isDst r
  let (free, victim) ← chooseScratch free fun r => !st.isFree r
  let edits ← resolveMoves p.moves free victim
  modify fun s => { s with edits := s.edits.modify b fun es => es ++ edits.map ((i, ·)) }
  -- The new state: survivors and definitions that are live.
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
where
  resolveMoves (moves : Array (Loc × Loc)) (free : List X86.GPR) (victim : X86.GPR) : M (Array Edit) := do
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

/-! ## Block boundaries -/

/-- Where a value is at the end of a block: its register, then its home. -/
def locsIn (s : RState) (v : VReg) : M (List Loc) := do
  let r := (s.reg[v]?).map Loc.reg |>.toList
  let h ← if s.home.contains v then pure [← homeOf v] else pure []
  return r ++ h

/-- The entry state of `s` reached from exit state `X` along an edge with
arguments `args`. -/
def decideEntry (s : Label) (X : RState) (args : List VReg) : M RState := do
  let cfg ← read
  let block := cfg.f.blocks[s]!
  let live := cfg.info.liveIn[s]!
  let mut E : RState := {}
  let nonParams := (live.toList.filter fun v => !block.params.contains v).toArray.qsort fun a b =>
    (cfg.info.weight.getD a 0 > cfg.info.weight.getD b 0) || (cfg.info.weight.getD a 0 == cfg.info.weight.getD b 0 && a < b)
  for v in nonParams do
    let inReg := X.reg[v]?
    match inReg with
    | some r =>
        if ← chance cfg.chaos.entryHome then E := { E with home := E.home.insert v }
        else E := E.put v r
    | none => E := { E with home := E.home.insert v }
    if X.home.contains v then E := { E with home := E.home.insert v }
  for (p, a) in block.params.zip args do
    if !live.contains p then continue
    let chaos ← chance cfg.chaos.entryHome
    match X.reg[a]? with
    | some r =>
        if E.isFree r && !chaos then E := E.put p r
        else
          match ← if chaos then pure none else pickReg E.isFree ((← get).hints[p]?) false with
          | some q => E := E.put p q
          | none => E := { E with home := E.home.insert p }
    | none =>
        match ← if chaos then pure none else pickReg E.isFree ((← get).hints[p]?) false with
        | some q => E := E.put p q
        | none => E := { E with home := E.home.insert p }
  return E

/-- The parallel move from exit state `X` to entry state `E` along an edge
binding `params := args`. -/
def edgeMoves (X E : RState) (params args : List VReg) : M (Array (Loc × Loc)) := do
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
      let s ← srcIn X src
      if s != h then moves := moves.push (h, s)
    else if !X.home.contains v then
      moves := moves.push (← homeOf v, ← srcIn X v)
  return moves

/-- The certificate of a block entered from exit state `X` (one predecessor):
the exit's facts after binding the parameters, for the live registers. -/
def certFromExit (s : Label) (X : RState) (args : List VReg) : M (List (Loc × List VReg)) := do
  let cfg ← read
  let block := cfg.f.blocks[s]!
  let live := cfg.info.liveIn[s]!
  let mut facts : List (Loc × List VReg) := []
  for v in live.toList do
    if block.params.contains v then continue
    for l in ← locsIn X v do facts := (l, [v]) :: facts
  for (p, a) in block.params.zip args do
    if live.contains p then
      for l in ← locsIn X a do facts := (l, [p]) :: facts
  return facts

def certOf (E : RState) : M (List (Loc × List VReg)) := do
  let mut facts : List (Loc × List VReg) := []
  for r in scratch do
    if let some v := E.get r then facts := (.reg r, [v]) :: facts
  for v in E.home.toList do facts := (← homeOf v, [v]) :: facts
  return facts

/-- Take edge `b → e.target` from exit state `X`. -/
def takeEdge (b : Label) (nEdges : Nat) (X : RState) (e : Edge VReg) : M Unit := do
  let cfg ← read
  let s := e.target
  let some block := cfg.f.blocks[s]? | throw s!"block {b}: edge to missing block {s}"
  let unique := cfg.info.preds[s]!.length == 1
  if !unique && nEdges != 1 then throw s!"block {b}: critical edge to block {s}"
  let live := cfg.info.liveIn[s]!
  -- What the edge carries: live registers that are not parameters, and the
  -- arguments of live parameters (exactly what the target's certificate
  -- may claim, so a borrowed victim always holds something known).
  let X := X.restrict fun v =>
    (live.contains v && !block.params.contains v) ||
      (block.params.zip e.args).any fun (p, a) => a == v && live.contains p
  let E ← match (← get).entry[s]! with
    | some E => pure E
    | none => do
        let E ← decideEntry s X e.args
        let cert ← if unique then certFromExit s X e.args else certOf E
        modify fun st => { st with entry := st.entry.set! s (some E), certs := st.certs.set! s (some cert) }
        -- Arguments on the other incoming edges prefer the parameters' registers.
        for q in cfg.info.preds[s]! do
          if q == b then continue
          for e' in cfg.f.blocks[q]!.term.edges do
            if e'.target != s then continue
            for (p, a) in block.params.zip e'.args do
              if let some r := E.reg[p]? then
                modify fun st => { st with hints := st.hints.insert a r }
        pure E
  let moves ← edgeMoves X E block.params e.args
  if moves.isEmpty then return
  let busy (r : X86.GPR) : Bool := !X.isFree r || !E.isFree r
  let free := scratch.filter (!busy ·)
  let (free, victim) ← chooseScratch free fun r => !X.isFree r
  let edits ← allocAt.resolveMoves moves free victim
  if unique then
    modify fun st => { st with edits := st.edits.modify s fun es => edits.map ((0, ·)) ++ es }
  else
    let n := cfg.f.blocks[b]!.body.size
    modify fun st => { st with edits := st.edits.modify b fun es => es ++ edits.map ((n, ·)) }

/-! ## Functions -/

def allocBlock (b : Label) : M Unit := do
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

/-- Allocate function `f` of a program. -/
def run (env : Xl.Env) (f : Func VReg) (chaos : Chaos := {}) : Except String Output := do
  let n := f.blocks.size
  if n == 0 then throw "a function without blocks"
  let info := analyse f
  if info.order.size != n then throw "unreachable blocks"
  let rng0 := mix64 (chaos.seed + 0x5eed)
  let order := if chaos.shuffle then
      (defaultOrder.zipIdx.toArray.qsort fun (a, i) (b, j) =>
        mix64 (rng0 + UInt64.ofNat (gprIndex a)) < mix64 (rng0 + UInt64.ofNat (gprIndex b)) ||
          (mix64 (rng0 + UInt64.ofNat (gprIndex a)) == mix64 (rng0 + UInt64.ofNat (gprIndex b)) && i < j)).toList.map (·.1)
    else defaultOrder
  let cfg : Cfg := { f, info, env, chaos, order, uses := f.blocks.map usePositions }
  -- The entry: parameters where the convention puts them.
  let mut homes : Std.HashMap VReg Loc := {}
  let mut E : RState := {}
  let mut cert : List (Loc × List VReg) := []
  for (p, i) in f.params.zipIdx do
    match Xl.paramLoc i with
    | .reg r =>
        if info.liveIn[0]!.contains p then E := E.put p r
    | l =>
        homes := homes.insert p l
        if info.liveIn[0]!.contains p then E := { E with home := E.home.insert p }
    cert := cert ++ [(Xl.paramLoc i, [p])]
  let st : St := { homes, rng := rng0
                   edits := Array.replicate n #[], locs := Array.replicate n #[]
                   termLocs := Array.replicate n [], certs := (Array.replicate n none).set! 0 (some cert)
                   entry := (Array.replicate n none).set! 0 (some E) }
  let go : M Unit := do for b in info.order do allocBlock b
  let ((), st) ← (go.run cfg).run st
  let blocks := (List.range n).map fun b =>
    { locs := st.locs[b]!.toList, termLocs := st.termLocs[b]!, edits := st.edits[b]!.toList
      cert := (st.certs[b]!).getD [] : BlockOut }
  return { blocks, numSlots := st.nextSlot }

end IxCC.Xv.Alloc.LinearScan
