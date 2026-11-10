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

/-! ## The oracle (untrusted) -/

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
path) to the list. -/
def backEdges (m : NatMap Block) (ok : Nat → Bool) :
    Nat → List Nat → NatSet × List (Nat × Nat) → Nat → NatSet × List (Nat × Nat)
  | 0, _, acc, _ => acc
  | fuel + 1, path, (seen, backs), b =>
      let path := b :: path
      (succsIn m ok b).foldl (init := (seen.insert b, backs)) fun (seen, backs) t =>
        if path.contains t then (seen, (b, t) :: backs)
        else if seen.contains t then (seen, backs)
        else backEdges m ok fuel path (seen, backs) t

/-- Predecessors within the group, from each member's successors. -/
def predsIn (m : NatMap Block) (ok : Nat → Bool) (members : List Nat) : NatMap (List Nat) :=
  members.foldl (init := {}) fun acc b =>
    (succsIn m ok b).foldl (init := acc) fun acc t => acc.insert t (b :: acc.getD t [])

/-- The natural loop of a back edge into `h`: `body` starts as `{h}`, and
the search walks predecessors backwards from the edge's source, one
frontier per unit of fuel, never past `h`. -/
def loopBody (preds : NatMap (List Nat)) : Nat → NatSet → List Nat → NatSet
  | 0, body, _ => body
  | _, body, [] => body
  | fuel + 1, body, frontier =>
      let fresh := frontier.filter (!body.contains ·)
      let body := fresh.foldl (fun s b => s.insert b) body
      loopBody preds fuel body (fresh.flatMap (preds.getD · []))

/-- A loop per header: the union of the natural loops of its back edges. -/
def addLoop (loops : List (Nat × NatSet)) (h : Nat) (body : NatSet) : List (Nat × NatSet) :=
  if loops.any (·.1 == h) then
    loops.map fun (h', b) => if h' == h then (h', body.toList.foldl (fun s x => s.insert x) b) else (h', b)
  else (h, body) :: loops

/-- The size of the smallest loop containing both blocks, else `none'`. -/
def sharedLoop (loops : List (Nat × NatSet)) (none' a b : Nat) : Nat :=
  loops.foldl (init := none') fun best (_, body) =>
    if body.contains a && body.contains b then min best body.size else best

/-- The first candidate with the smallest score. -/
def pickBest (score : Nat → Nat) : List Nat → Option Nat
  | [] => none
  | c :: cs =>
      match pickBest score cs with
      | some d => if score d < score c then some d else some c
      | none => some c

/-- Place `b`, then keep following the unplaced successor that stays in the
smallest loop shared with the block just placed. The placed blocks are a
set and a list in reverse order. -/
def extendChain (m : NatMap Block) (ok : Nat → Bool) (loops : List (Nat × NatSet)) (none' : Nat) :
    Nat → NatSet × List Nat → Nat → NatSet × List Nat
  | 0, placed, _ => placed
  | fuel + 1, (done, order), b =>
      let done := done.insert b
      let order := b :: order
      match pickBest (sharedLoop loops none' b) ((succsIn m ok b).filter (!done.contains ·)) with
      | some t => extendChain m ok loops none' fuel (done, order) t
      | none => (done, order)

/-- Start a chain at the unplaced block sharing the smallest loop with the
last block placed (the first pending block when none does, or when nothing
is placed yet), until every pending block is placed. -/
def chains (m : NatMap Block) (ok : Nat → Bool) (loops : List (Nat × NatSet)) (none' bound : Nat) :
    Nat → NatSet × List Nat → List Nat → NatSet × List Nat
  | 0, placed, _ => placed
  | fuel + 1, (done, order), pending =>
      match pending.filter (!done.contains ·) with
      | [] => (done, order)
      | first :: rest =>
          let start := match order.head? with
            | some last => (pickBest (sharedLoop loops none' last) (first :: rest)).getD first
            | none => first
          chains m ok loops none' bound fuel (extendChain m ok loops none' bound (done, order) start)
            (first :: rest)

/-- One group's order: the entry, chains through hot blocks, then the cold
blocks in index order. -/
def groupOrder (m : NatMap Block) (seen : NatSet) (g : Group) : List Nat :=
  let members := ((List.range g.count).map (g.start + ·)).filter seen.contains
  let isCold (b : Nat) : Bool := g.cold.contains b && g.entry != some b
  let hot := members.filter (!isCold ·)
  let cold := members.filter isCold
  let ok (t : Nat) : Bool := g.contains t && seen.contains t && !isCold t
  let start := match g.entry with
    | some e => if seen.contains e then [e] else []
    | none => []
  let pending := start ++ hot
  let fuel := members.length + 1
  let (_, backs) := pending.foldl (init := (({} : NatSet), ([] : List (Nat × Nat)))) fun acc r =>
    if acc.1.contains r then acc else backEdges m ok fuel [] acc r
  let preds := predsIn m ok hot
  let loops := backs.foldl (init := []) fun loops (u, h) =>
    addLoop loops h (loopBody preds fuel (({} : NatSet).insert h) [u])
  (chains m ok loops fuel fuel fuel ({}, []) pending).2.reverse ++ cold

def Order.produce (p : Program) (s : Shape) : Order :=
  let m := blockMap p
  let seen := reachable p s.roots
  s.groups.map (groupOrder m seen)

end IxCC.X86.Layout
