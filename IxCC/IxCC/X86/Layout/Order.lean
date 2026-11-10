import IxCC.X86.Layout.Basic

/-!
# Block order (layout step 2 of 3)

The order is certificate data: an untrusted oracle (`Order.produce`)
proposes, per group, the blocks in layout order, and `Order.check`, on the
recheck path, accepts it only if

- there is one list per group, naming only that group's blocks;
- no block appears twice, and every block is a block of the program;
- every block reachable from the entry and the roots appears, so every
  target of a laid-out block is laid out;
- a reachable group entry comes first in its group (CompCert
  `Linearize.v`), and the program entry is laid out;
- every target of a laid-out block is laid out, checked directly
  (`placedClosed`), which is what `Proof.Order.check_sound` gives the
  linearisation proof.

Blocks left out are unreachable and dropped.

The oracle is loop-aware. It finds each group's natural loops (a back edge
`u → h` of a depth-first search from the entry, and the blocks that reach
`u` without passing `h`), places the entry first, and grows chains: from
each placed block it follows the unplaced successor that stays in the
smallest loop it shares with that block, preferring a branch's false edge
(which then falls through), then its true edge, or a jump's target. When a
chain ends, the next one starts at the unplaced block sharing the smallest
loop with the last block placed, else at the first unplaced block in index
order. So a loop's header and body are contiguous, its exits follow it,
and a simple loop takes one taken branch per iteration (its back edge).
Cold blocks (failure and slow paths) go last. The oracle runs on fuel and
persistent maps, like the check, so the kernel can evaluate it too.
-/

namespace IxCC.X86.Layout

/-- Per group, the blocks in layout order. -/
abbrev Order := List (List Nat)

/-- Every target of a placed block is placed: so a run that starts at a
placed block never leaves the laid-out blocks (the linearisation proof
relies on this local check rather than on the reachability walk's fuel). -/
def placedClosed (p : Program) (placed : NatSet) : Bool :=
  p.blocks.toList.zipIdx.all fun (blk, b) =>
    !placed.contains b || blk.targets.all fun t => placed.contains t.toNat

/-- The recheck-path validator of a proposed order. -/
def Order.check (p : Program) (s : Shape) (o : Order) : Bool :=
  let seen := reachable p s.roots
  let flat := o.flatten
  let placed : NatSet := flat.foldl (fun acc b => acc.insert b) {}
  o.length == s.groups.length &&
  placed.size == flat.length &&
  flat.all (· < p.blocks.size) &&
  (s.groups.zip o).all (fun (g, bs) =>
    bs.all g.contains &&
      match g.entry with
      | some e => !seen.contains e || bs.head? == some e
      | none => true) &&
  seen.toList.all placed.contains &&
  placed.contains p.entry.toNat &&
  placedClosed p placed

/-! ## The oracle (untrusted)

Its cost is near-linear in a group's blocks and edges: the depth-first search
keeps the blocks on its current path in a set; the loops are found once per
header, from all its back edges at once, by a breadth-first walk that expands
each block once; each block knows the loops containing it, smallest first;
and the next chain's start is found from per-loop cursors over the loops'
blocks in index order, which only move forward. -/

/-- Successors in order of preference: a branch's false edge (which can
fall through), then its true edge; a jump's target. -/
def preferred (b : Block) : List Nat :=
  match b.terminator with
  | .branch _ _ _ yes no _ => [no.toNat, yes.toNat]
  | .jump t => [t.toNat]
  | _ => []

/-- A block's preferred successors among the blocks `ok` accepts. -/
def succsIn (m : NatMap Block) (ok : Nat → Bool) (b : Nat) : List Nat :=
  (((m.get? b).map preferred).getD []).filter ok

/-- Depth-first search from `b` (depth bounded by the fuel), adding the
blocks it visits to `seen` and each back edge `(u, h)` (`h` on the current
path, the set `onPath`) to the list. -/
def backEdges (m : NatMap Block) (ok : Nat → Bool) :
    Nat → NatSet → NatSet × List (Nat × Nat) → Nat → NatSet × List (Nat × Nat)
  | 0, _, acc, _ => acc
  | fuel + 1, onPath, (seen, backs), b =>
      let onPath := onPath.insert b
      (succsIn m ok b).foldl (init := (seen.insert b, backs)) fun (seen, backs) t =>
        if onPath.contains t then (seen, (b, t) :: backs)
        else if seen.contains t then (seen, backs)
        else backEdges m ok fuel onPath (seen, backs) t

/-- Predecessors within the group, from each member's successors. -/
def predsIn (m : NatMap Block) (ok : Nat → Bool) (members : List Nat) : NatMap (List Nat) :=
  members.foldl (init := {}) fun acc b =>
    (succsIn m ok b).foldl (init := acc) fun acc t => acc.insert t (b :: acc.getD t [])

/-- The loop of a header: `body` starts as `{h}`, and the search walks
predecessors backwards from the sources of the back edges into `h`, one
frontier per unit of fuel, never past `h`, so it collects the union of their
natural loops. A block the frontier lists more than once is expanded once:
otherwise every two-way branch inside the loop would double the frontier. -/
def loopBody (preds : NatMap (List Nat)) : Nat → NatSet → List Nat → NatSet
  | 0, body, _ => body
  | _, body, [] => body
  | fuel + 1, body, frontier =>
      let (body, fresh) := frontier.foldl (init := (body, ([] : List Nat))) fun (s, acc) b =>
        if s.contains b then (s, acc) else (s.insert b, b :: acc)
      loopBody preds fuel body (fresh.flatMap (preds.getD · []))

/-- Insert `x` into a list ordered by its first component. -/
def insertBySize (x : Nat × Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [x]
  | y :: ys => if x.1 ≤ y.1 then x :: y :: ys else y :: insertBySize x ys

/-- For each block, the loops containing it, as `(size, header)`, smallest
first. -/
def loopsOf (loops : List (Nat × NatSet)) : NatMap (List (Nat × Nat)) :=
  loops.foldl (init := {}) fun acc (h, body) =>
    body.toList.foldl (init := acc) fun acc x => acc.insert x (insertBySize (body.size, h) (acc.getD x []))

/-- The size of the smallest loop containing both blocks, else `none'`. -/
def sharedLoop (byBlock : NatMap (List (Nat × Nat))) (loops : NatMap NatSet) (none' a b : Nat) : Nat :=
  (byBlock.getD a []).foldl (init := none') fun best (size, h) =>
    if ((loops.get? h).map (·.contains b)).getD false then min best size else best

/-- The first candidate with the smallest score. -/
def pickBest (score : Nat → Nat) : List Nat → Option Nat
  | [] => none
  | c :: cs =>
      match pickBest score cs with
      | some d => if score d < score c then some d else some c
      | none => some c

/-- Place `b`, then keep following the unplaced successor that stays in the
smallest loop shared with the block just placed (`shared`). The placed
blocks are a set and a list in reverse order. -/
def extendChain (m : NatMap Block) (ok : Nat → Bool) (shared : Nat → Nat → Nat) :
    Nat → NatSet × List Nat → Nat → NatSet × List Nat
  | 0, placed, _ => placed
  | fuel + 1, (done, order), b =>
      let done := done.insert b
      let order := b :: order
      match pickBest (shared b) ((succsIn m ok b).filter (!done.contains ·)) with
      | some t => extendChain m ok shared fuel (done, order) t
      | none => (done, order)

/-- `xs` from its first unplaced block on. -/
def dropPlaced (done : NatSet) : List Nat → List Nat
  | [] => []
  | x :: xs => if done.contains x then dropPlaced done xs else x :: xs

/-- Among the loops containing a block (`(size, header)`, smallest first), the
first unplaced block in index order of those of the smallest size that still
have one, with each loop's cursor (its blocks in index order, from its first
unplaced one) moved forward; `best` is the size and block found so far. -/
def loopStart (done : NatSet) :
    List (Nat × Nat) → Option (Nat × Nat) → NatMap (List Nat) → Option Nat × NatMap (List Nat)
  | [], best, cursors => (best.map (·.2), cursors)
  | (size, h) :: rest, best, cursors =>
      let larger := match best with
        | some (s, _) => decide (s < size)
        | none => false
      if larger then (best.map (·.2), cursors)
      else
        let cur := dropPlaced done (cursors.getD h [])
        let cursors := cursors.insert h cur
        match cur with
        | [] => loopStart done rest best cursors
        | x :: _ =>
            let best := match best with
              | some (_, y) => some (size, min x y)
              | none => some (size, x)
            loopStart done rest best cursors

/-- Start a chain at the unplaced block sharing the smallest loop with the
last block placed (the first pending block when none does, or when nothing
is placed yet), until every pending block is placed. After the first chain
(which places the entry) the pending blocks are in index order, so the first
unplaced one sharing the smallest loop is the one of least index among the
loops of that size containing the last block (`loopStart`). -/
def chains (m : NatMap Block) (ok : Nat → Bool) (shared : Nat → Nat → Nat)
    (byBlock : NatMap (List (Nat × Nat))) (bound : Nat) :
    Nat → NatSet × List Nat → List Nat → NatMap (List Nat) → NatSet × List Nat
  | 0, placed, _, _ => placed
  | fuel + 1, (done, order), pending, cursors =>
      match dropPlaced done pending with
      | [] => (done, order)
      | first :: rest =>
          let (start, cursors) := match order.head? with
            | some last =>
                let (s, cursors) := loopStart done (byBlock.getD last []) none cursors
                (s.getD first, cursors)
            | none => (first, cursors)
          chains m ok shared byBlock bound fuel (extendChain m ok shared bound (done, order) start)
            (first :: rest) cursors

/-- One group's order: the entry, chains through hot blocks, then the cold
blocks in index order. -/
def groupOrder (m : NatMap Block) (seen : NatSet) (g : Group) : List Nat :=
  let coldSet : NatSet := g.cold.foldl (fun s b => s.insert b) {}
  let members := ((List.range g.count).map (g.start + ·)).filter seen.contains
  let isCold (b : Nat) : Bool := coldSet.contains b && g.entry != some b
  let hot := members.filter (!isCold ·)
  let cold := members.filter isCold
  let ok (t : Nat) : Bool := g.contains t && seen.contains t && !isCold t
  let start := match g.entry with
    | some e => if seen.contains e then [e] else []
    | none => []
  let pending := start ++ hot
  let fuel := members.length + 1
  let (_, backs) := pending.foldl (init := (({} : NatSet), ([] : List (Nat × Nat)))) fun acc r =>
    if acc.1.contains r then acc else backEdges m ok fuel {} acc r
  let preds := predsIn m ok hot
  -- the back edges' sources, by header
  let latches : NatMap (List Nat) := backs.foldl (init := {}) fun acc (u, h) => acc.insert h (u :: acc.getD h [])
  let loops : List (Nat × NatSet) :=
    latches.toList.map fun (h, us) => (h, loopBody preds fuel (({} : NatSet).insert h) us)
  let loopMap : NatMap NatSet := loops.foldl (init := {}) fun acc (h, body) => acc.insert h body
  let byBlock := loopsOf loops
  let cursors : NatMap (List Nat) := loops.foldl (init := {}) fun acc (h, body) => acc.insert h body.toList
  (chains m ok (sharedLoop byBlock loopMap fuel) byBlock fuel fuel ({}, []) pending cursors).2.reverse ++ cold

def Order.produce (p : Program) (s : Shape) : Order :=
  let m := blockMap p
  let seen := reachable p s.roots
  s.groups.map (groupOrder m seen)

end IxCC.X86.Layout
