import IxCC.X86.Basic

/-!
# Block layout: groups, targets and reachability

The layout passes (tunnelling, block order, linearisation) work on a
typed program whose blocks come in *groups*: contiguous ranges that are
laid out together, each a function, an export wrapper, or the shared exit
group of failure blocks. Stacking produces the groups; the order oracle
permutes blocks within each group; linearisation renumbers.

Everything here is in kernel-evaluable style (D17): blocks are read once
into a persistent `Nat`-keyed map, and graph walks run on fuel. -/

namespace IxCC.X86.Layout

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
def _root_.IxCC.X86.Block.targets (b : Block) : List BlockId :=
  b.instructions.toList.filterMap (fun | .call t => some t | _ => none) ++
    match b.terminator with
    | .jump t | .tailCall t => [t]
    | .branch _ _ _ yes no _ => [yes, no]
    | .ret => []

/-- One breadth-first step: the frontier's blocks not seen yet join `seen`, and
the next frontier is their targets. A block the frontier lists more than once
is expanded once: otherwise every balanced join would double the
frontier. -/
def reachStep (m : NatMap Block) (seen : NatSet) (frontier : List Nat) : NatSet × List Nat :=
  let fresh := frontier.filter (!seen.contains ·)
  let seen := fresh.foldl (fun s b => s.insert b) seen
  let dedupFresh := (fresh.foldl (init := (({} : NatSet), [])) fun (s, acc) b =>
    if s.contains b then (s, acc) else (s.insert b, b :: acc)).2.reverse
  let next := dedupFresh.flatMap fun b => ((m.get? b).map fun blk => blk.targets.map UInt32.toNat).getD []
  (seen, next)

/-- Breadth-first reachability, one frontier (`reachStep`) per unit of fuel. -/
def reach (m : NatMap Block) : Nat → NatSet → List Nat → NatSet
  | 0, seen, _ => seen
  | _, seen, [] => seen
  | fuel + 1, seen, frontier =>
      match reachStep m seen frontier with
      | (seen, next) => reach m fuel seen next

/-- The blocks reachable from the program entry and the roots. -/
def reachable (p : Program) (roots : List Nat) : NatSet :=
  reach (blockMap p) (p.blocks.size + 1) {} (p.entry.toNat :: roots)

end IxCC.X86.Layout
