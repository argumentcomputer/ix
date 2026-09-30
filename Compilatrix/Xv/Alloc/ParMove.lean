import Compilatrix.Xv.Alloc.Output

/-!
# Parallel moves (untrusted)

A port of regalloc2's resolver (`src/moves.rs`, 05 §5; review §1.1 Q4). A
parallel move `{dᵢ ← sᵢ}` with distinct destinations reads every source,
then writes every destination. `sequence` orders it: each move precedes the
one that overwrites its source, and since each location has one writer the
dependency graph's cycles are simple, so a depth-first walk emits moves in
postorder and breaks each cycle through a scratch location. `expand` then
picks the scratch (a free register, else an extra slot) and rewrites stack
cell to stack cell moves through a register: a free one, or a borrowed
"victim" saved to a second extra slot and restored afterwards
(`MoveAndScratchResolver::compute`).

Nothing here is trusted: the validator checks the resulting edits one move
at a time, so a wrong sequence is rejected, not miscompiled. The victim's
save and restore validate because a move copies its source's facts (gap 1
closed), so the restored register regains exactly what it held.
-/

namespace Compilatrix.Xv.Alloc.ParMove

/-- A location or the scratch. -/
abbrev Slot := Option Loc

/-- Sequence parallel moves `(dst, src)` (distinct destinations). The result
may name the scratch (`none`); the flag says whether it does. -/
def sequence (moves : Array (Loc × Loc)) : Array (Slot × Slot) × Bool := Id.run do
  -- Drop self-moves and duplicates.
  let mut ms : Array (Loc × Loc) := #[]
  for m in moves do
    if m.1 != m.2 && !ms.contains m then ms := ms.push m
  let plain := ms.map fun (d, s) => (some d, some s)
  if ms.size ≤ 1 then return (plain, false)
  let dsts := ms.map (·.1)
  if !ms.any (fun (_, s) => dsts.contains s) then return (plain, false)
  -- The move that must come after move `i`: the one overwriting its source.
  let after : Array (Option Nat) := ms.map fun (_, s) => dsts.findIdx? (· == s)
  -- 0 = to do, 1 = on the stack, 2 = done.
  let mut state := Array.replicate ms.size 0
  let mut out : Array (Slot × Slot) := #[]
  let mut usedScratch := false
  for start in [:ms.size] do
    if state[start]! != 0 then continue
    let mut stack : Array Nat := #[start]
    state := state.set! start 1
    for _ in [:2 * ms.size + 2] do
      if stack.isEmpty then break
      let top := stack.back!
      match after[top]! with
      | some next =>
          if state[next]! == 0 then
            stack := stack.push next
            state := state.set! next 1
          else if state[next]! == 2 then
            for _ in [:stack.size] do
              match stack.back? with
              | some t =>
                  out := out.push (some ms[t]!.1, some ms[t]!.2)
                  state := state.set! t 2
                  stack := stack.pop
              | none => break
          else
            -- A cycle through `next`: `top`'s destination is written from
            -- the scratch, which is loaded (after reversal: first) from
            -- `top`'s source.
            state := state.set! top 2
            stack := stack.pop
            let (d, s) := ms[top]!
            usedScratch := true
            out := out.push (some d, none)
            for _ in [:stack.size] do
              match stack.back? with
              | some t =>
                  stack := stack.pop
                  state := state.set! t 2
                  out := out.push (some ms[t]!.1, some ms[t]!.2)
                  if t == next then break
              | none => break
            out := out.push (none, some s)
      | none =>
          for _ in [:stack.size] do
            match stack.back? with
            | some t =>
                out := out.push (some ms[t]!.1, some ms[t]!.2)
                state := state.set! t 2
                stack := stack.pop
            | none => break
  return (out.reverse, usedScratch)

/-- Where the scratch and the victim come from. -/
structure Scratch where
  /-- Registers free at this point, in preference order. -/
  free : List X86.GPR
  /-- An extra slot for a cycle when no register is free. -/
  cycleSlot : Loc
  /-- The register to borrow for cell-to-cell moves when none is free. -/
  victim : X86.GPR
  /-- An extra slot saving the victim. -/
  saveSlot : Loc

/-- What `expand` used, so the caller can size the frame. -/
structure Used where
  cycleSlot : Bool := false
  saveSlot : Bool := false
  deriving Inhabited

/-- Resolve a parallel move into single moves with no cell-to-cell move. -/
def resolve (moves : Array (Loc × Loc)) (sc : Scratch) : Array Edit × Used := Id.run do
  let (seq, needsScratch) := sequence moves
  let mut free := sc.free
  let mut used : Used := {}
  let scratch : Loc ← if needsScratch then
      match free with
      | r :: rest => do free := rest; pure (.reg r)
      | [] => do used := { used with cycleSlot := true }; pure sc.cycleSlot
    else pure sc.cycleSlot
  let fill (x : Slot) : Loc := x.getD scratch
  let ms : Array (Loc × Loc) := seq.map fun (d, s) => (fill d, fill s)
  if !ms.any (fun (d, s) => d.isCell && s.isCell) then
    return (ms.map fun (d, s) => .move d s, used)
  let (reg, save) := match free with
    | r :: _ => (r, none)
    | [] => (sc.victim, some sc.saveSlot)
  if save.isSome then used := { used with saveSlot := true }
  let scratchReg : Loc := .reg reg
  let mut scratchDirty := false
  let mut saveDirty := true
  let mut out : Array Edit := #[]
  for (d, s) in ms do
    if d.isCell && s.isCell then
      if let some slot := save then
        if saveDirty then
          out := out.push (.move slot scratchReg)
          saveDirty := false
      out := out.push (.move scratchReg s)
      out := out.push (.move d scratchReg)
      scratchDirty := true
    else
      if s == scratchReg && scratchDirty then
        if let some slot := save then
          out := out.push (.move scratchReg slot)
        scratchDirty := false
      if d == scratchReg then
        scratchDirty := false
        saveDirty := true
      out := out.push (.move d s)
  if let some slot := save then
    if scratchDirty then out := out.push (.move scratchReg slot)
  return (out, used)

/-- Run moves on a concrete assignment of values to locations (for tests):
the parallel meaning, and the sequential meaning of edits. -/
def runParallel (moves : List (Loc × Loc)) (vals : Loc → Option Nat) : Loc → Option Nat :=
  fun l => match moves.find? (·.1 == l) with
    | some (_, s) => vals s
    | none => vals l

def runSequential (edits : List Edit) (vals : Loc → Option Nat) : Loc → Option Nat :=
  edits.foldl (fun v e => match e with
    | .move d s => fun l => if l == d then v s else v l) vals

end Compilatrix.Xv.Alloc.ParMove
