import IxCC.X86.Layout.Order
import IxCC.X86.Eval

/-!
# Linearisation (05 §7, step 3)

Given a checked order, renumber the blocks by their position in it, map
every call, jump, branch and tail-call target and the entry through the
renumbering, and invert a branch whose true target is the next block and
whose false target is not: `branch c yes no` becomes `branch c.negate no
yes`, so the false edge is the one that falls through. A branch whose false
target is then the next block is marked `fall`: E2 encodes only its `jcc`
and checks that the next block starts where the `jcc` ends. A
proved-once, re-run pass (P, 05 §1.1).

`Condition.negate_holds` and `Flags.test_negate` are what inversion needs:
the negated condition holds exactly when the original does not, on the
flags as well as mathematically, and it reads the same flags
(`negate_reads`), so the producer still defines them
(`Terminator.wellFormed_negate`). `executeTerminator_negate`: an inverted
branch goes where the original goes. The `Reach` mark changes neither
(`executeTerminator_reach`, `Terminator.wellFormed_reach`).
-/

namespace IxCC.X86

/-- The complementary condition. -/
def Condition.negate : Condition → Condition
  | .eq => .ne
  | .ne => .eq
  | .unsignedLt => .unsignedGe
  | .unsignedGe => .unsignedLt
  | .unsignedLe => .unsignedGt
  | .unsignedGt => .unsignedLe
  | .signedLt => .signedGe
  | .signedGe => .signedLt
  | .signedLe => .signedGt
  | .signedGt => .signedLe

theorem Condition.negate_negate (c : Condition) : c.negate.negate = c := by
  cases c <;> rfl

theorem Condition.negate_reads (c : Condition) : c.negate.reads = c.reads := by
  cases c <;> rfl

theorem Condition.negate_holds (c : Condition) (width : Width) (left right : Word) :
    c.negate.holds width left right = !(c.holds width left right) := by
  cases c <;> simp only [Condition.negate, Condition.holds] <;>
    generalize width.truncate left = a <;> generalize width.truncate right = b <;>
    generalize width.signedValue left = x <;> generalize width.signedValue right = y <;>
    simp only [← decide_not, UInt64.not_lt, UInt64.not_le, Int.not_lt, Int.not_le, bne, Bool.not_not]

theorem ByteEval.Flags.test_negate (flags : ByteEval.Flags) (c : Condition) :
    flags.test c.negate = (flags.test c).map (!·) := by
  obtain ⟨carry, zero, sign, overflow⟩ := flags
  cases c <;> cases carry <;> cases zero <;> cases sign <;> cases overflow <;>
    simp [Condition.negate, ByteEval.Flags.test]

theorem Terminator.wellFormed_negate (producer : Op) (args : List Arg) (c : Condition) (yes no : BlockId) :
    (Terminator.branch producer args c.negate no yes).wellFormed =
      (Terminator.branch producer args c yes no).wellFormed := by
  simp [Terminator.wellFormed, FusedOk, desc, Table.jccDesc, Op.jccRel32, Condition.negate_reads]

/-- An inverted branch goes where the original goes, with the same core. -/
theorem executeTerminator_negate (checked : Checked) (machine : Machine) (producer : Op) (args : List Arg)
    (c : Condition) (yes no : BlockId) {core : Core} {flags : ByteEval.Flags} {take : Bool}
    (produced : producer.exec args machine.core {} = .ok (core, flags)) (tested : flags.test c = some take) :
    executeTerminator checked (.branch producer args c.negate no yes) machine =
      executeTerminator checked (.branch producer args c yes no) machine := by
  simp only [executeTerminator, produced, ByteEval.Flags.test_negate, tested, Option.map_some]
  cases take <;> rfl

/-- A branch's `Reach` is an encoding annotation: the typed semantics
ignores it. -/
theorem executeTerminator_reach (checked : Checked) (machine : Machine) (producer : Op) (args : List Arg)
    (c : Condition) (yes no : BlockId) (reach : Reach) :
    executeTerminator checked (.branch producer args c yes no reach) machine =
      executeTerminator checked (.branch producer args c yes no) machine := rfl

theorem Terminator.wellFormed_reach (producer : Op) (args : List Arg) (c : Condition) (yes no : BlockId)
    (reach : Reach) :
    (Terminator.branch producer args c yes no reach).wellFormed =
      (Terminator.branch producer args c yes no).wellFormed := rfl

namespace Layout

/-- Renumber the blocks by their position in `order` and invert branches
whose true target is next. -/
def linearize (p : Program) (order : List Nat) : Program × NatMap Nat :=
  let m := blockMap p
  let pos : NatMap Nat := order.zipIdx.foldl (fun acc (b, i) => acc.insert b i) {}
  let rn (t : BlockId) : BlockId := UInt32.ofNat ((pos.get? t.toNat).getD t.toNat)
  let blocks := order.zipIdx.map fun (b, i) =>
    let blk := (m.get? b).getD default
    let instructions := blk.instructions.toList.map fun
      | .call t => .call (rn t)
      | instruction => instruction
    let terminator : Terminator := match blk.terminator with
      | .jump t => .jump (rn t)
      | .tailCall t => .tailCall (rn t)
      | .ret => .ret
      | .branch producer args c yes no _ =>
          let yes := rn yes
          let no := rn no
          if yes.toNat == i + 1 && no.toNat != i + 1 then .branch producer args c.negate no yes .fall
          else if no.toNat == i + 1 then .branch producer args c yes no .fall
          else .branch producer args c yes no
    ({ instructions := instructions.toArray, terminator } : Block)
  ({ blocks := blocks.toArray, entry := rn p.entry }, pos)

/-- Check the order, then linearise. The map sends old block indices to new. -/
def run (p : Program) (s : Shape) (o : Order) : Except String (Program × NatMap Nat) :=
  if Order.check p s o then pure (linearize p o.flatten)
  else throw "layout: the block order fails its check"

end Layout

end IxCC.X86
