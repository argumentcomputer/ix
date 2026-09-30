import Compilatrix.X86.Layout.Basic

/-!
# Block order (05 §7, step 2)

The order is certificate data: an untrusted oracle (`Order.produce`)
proposes, per group, the blocks in layout order, and `Order.check`, on the
recheck path, accepts it only if

- there is one list per group, naming only that group's blocks;
- no block appears twice, and every block is a block of the program;
- every block reachable from the entry and the roots appears, so every
  target of a laid-out block is laid out;
- a reachable group entry comes first in its group (CompCert
  `Linearize.v`), and the program entry is laid out.

Blocks left out are unreachable and dropped. The oracle places each
group's entry first and then follows the likely successor of each block
(a branch's false edge, then its true edge, or a jump's target), skipping
cold blocks, which go last; blocks the chains miss follow in index order.
-/

namespace Compilatrix.X86.Layout

/-- Per group, the blocks in layout order. -/
abbrev Order := List (List Nat)

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
  placed.contains p.entry.toNat

/-! ## The oracle (untrusted) -/

/-- Successors in order of preference: a branch's false edge (which can
fall through), then its true edge; a jump's target. -/
def preferred (b : Block) : List Nat :=
  match b.terminator with
  | .branch _ _ _ yes no => [no.toNat, yes.toNat]
  | .jump t => [t.toNat]
  | _ => []

/-- Place `b`, then keep following the first acceptable unplaced
successor. `placed` is in reverse order. -/
def extendChain (m : NatMap Block) (ok : Nat → Bool) : Nat → List Nat → Nat → List Nat
  | 0, placed, _ => placed
  | fuel + 1, placed, b =>
      let placed := b :: placed
      match (((m.get? b).map preferred).getD []).find? (fun t => ok t && !placed.contains t) with
      | some t => extendChain m ok fuel placed t
      | none => placed

/-- Start a chain at each candidate not yet placed. -/
def chains (m : NatMap Block) (ok : Nat → Bool) (bound : Nat) : List Nat → List Nat → List Nat
  | [], placed => placed
  | c :: cs, placed =>
      if placed.contains c then chains m ok bound cs placed
      else chains m ok bound cs (extendChain m ok bound placed c)

/-- One group's order: the entry, chains through hot blocks, then the
cold blocks in index order. -/
def groupOrder (m : NatMap Block) (seen : NatSet) (g : Group) : List Nat :=
  let members := ((List.range g.count).map (g.start + ·)).filter seen.contains
  let hot := members.filter (!g.cold.contains ·)
  let cold := members.filter g.cold.contains
  let ok (t : Nat) : Bool := g.contains t && seen.contains t && !g.cold.contains t
  let start := match g.entry with
    | some e => if seen.contains e then [e] else []
    | none => []
  (chains m ok (members.length + 1) (start ++ hot) []).reverse ++ cold

def Order.produce (p : Program) (s : Shape) : Order :=
  let m := blockMap p
  let seen := reachable p s.roots
  s.groups.map (groupOrder m seen)

end Compilatrix.X86.Layout
