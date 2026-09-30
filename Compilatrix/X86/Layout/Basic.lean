import Compilatrix.X86.Basic

/-!
# Block layout: groups, targets and reachability (05 §7)

The layout passes (tunnelling, block order, linearisation) work on a
typed program whose blocks come in *groups*: contiguous ranges that are
laid out together, each a function, an export wrapper, or the shared exit
group of failure blocks. Stacking produces the groups; the order oracle
permutes blocks within each group; linearisation renumbers.

Everything here is in kernel-evaluable style (00): blocks are read once
into a persistent `Nat`-keyed map, and graph walks run on fuel.
-/

namespace Compilatrix.X86.Layout

abbrev NatMap (α : Type) := Std.TreeMap Nat α compare
abbrev NatSet := Std.TreeSet Nat compare

/-- A contiguous range of blocks laid out together. -/
structure Group where
  start : Nat
  count : Nat
  /-- The group's entry, placed first; `none` for a set of independent
  targets (the exit group). -/
  entry : Option Nat := none
  /-- Blocks to place last: failure and slow paths. -/
  cold : List Nat := []
  deriving DecidableEq, Repr, Inhabited

def Group.contains (g : Group) (b : Nat) : Bool := decide (g.start ≤ b) && decide (b < g.start + g.count)

/-- How a program's blocks are grouped, and where execution may start. -/
structure Shape where
  groups : List Group
  /-- Entry points (the export wrappers). Every block reachable from one is
  laid out; the rest are dropped. -/
  roots : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The blocks by index, read once. -/
def blockMap (p : Program) : NatMap Block :=
  p.blocks.toList.zipIdx.foldl (fun m (b, i) => m.insert i b) {}

/-- Every block a block may transfer control to: call targets, then its
terminator's targets. -/
def _root_.Compilatrix.X86.Block.targets (b : Block) : List BlockId :=
  b.instructions.toList.filterMap (fun | .call t => some t | _ => none) ++
    match b.terminator with
    | .jump t | .tailCall t => [t]
    | .branch _ _ _ yes no _ => [yes, no]
    | .ret => []

/-- Breadth-first reachability, one frontier per unit of fuel. -/
def reach (m : NatMap Block) : Nat → NatSet → List Nat → NatSet
  | 0, seen, _ => seen
  | _, seen, [] => seen
  | fuel + 1, seen, frontier =>
      let fresh := frontier.filter (!seen.contains ·)
      let seen := fresh.foldl (fun s b => s.insert b) seen
      let next := fresh.flatMap fun b => ((m.get? b).map fun blk => blk.targets.map UInt32.toNat).getD []
      reach m fuel seen next

/-- The blocks reachable from the program entry and the roots. -/
def reachable (p : Program) (roots : List Nat) : NatSet :=
  reach (blockMap p) (p.blocks.size + 1) {} (p.entry.toNat :: roots)

end Compilatrix.X86.Layout
