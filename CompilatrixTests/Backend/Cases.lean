import Compilatrix.Backend
import CompilatrixTests.Backend.Programs

/-!
# Backend cases checked while this module elaborates

Cheap assertions on the pieces of M1.B5: the frame layout oracle and the
check's rejections (overlap, alignment, bounds, missing or extra saves,
16-byte alignment at calls, frameless with calls, size), when the
prologue checks the stack, the shape of what stacking emits (the exit
group, the wrapper, prologues and epilogues, a tail call as a jump), the
programs stacking rejects, tunnelling to the exit group, the block order
check's rejections, and branch inversion.
-/

namespace CompilatrixTests.Backend.Cases

open Compilatrix Compilatrix.Xv Compilatrix.Xv.Stacking CompilatrixTests.Backend.Programs

/-! ## Frame layouts -/

def factsOf (p : LProgram) (fn : Nat) : Facts := (p.funcs[fn]!).facts

-- `calls`: one slot, a call, and `rbx` written.
def callsFacts : Facts := factsOf calls 0

#guard callsFacts.calls && callsFacts.slots == 1 && saves callsFacts == [.rbx]

-- The oracle: the slot, then the save, rounded to 16 with the return address.
def callsLayout : FrameLayout := FrameLayout.produce callsFacts

#guard callsLayout == { size := 24, slotOff := [0], saveOff := [(.rbx, 8)], outArgs := 0 }
#guard callsLayout.check callsFacts
#guard FrameLayout.checked callsFacts callsLayout

-- A slot on the save's cell, misaligned, or past the frame; a slot without a cell.
#guard !({ callsLayout with slotOff := [8] } : FrameLayout).check callsFacts
#guard !({ callsLayout with slotOff := [4] } : FrameLayout).check callsFacts
#guard !({ callsLayout with slotOff := [24] } : FrameLayout).check callsFacts
#guard !({ callsLayout with slotOff := [] } : FrameLayout).check callsFacts
-- A written callee-saved register left unsaved; a register saved that is not written.
#guard !({ callsLayout with saveOff := [] } : FrameLayout).check callsFacts
#guard !({ callsLayout with size := 40, saveOff := [(.rbx, 8), (.r12, 16)] } : FrameLayout).check callsFacts
-- rsp misaligned at the calls; frameless despite the calls; too big for the slack and disp32.
#guard !({ callsLayout with size := 16 } : FrameLayout).check callsFacts
#guard !({ callsLayout with size := 0, slotOff := [], saveOff := [] } : FrameLayout).check callsFacts
#guard !({ callsLayout with size := 2 ^ 20 - 8 } : FrameLayout).check callsFacts

-- `stackArgs`: two outgoing argument cells below the frame.
def stackArgsFacts : Facts := factsOf stackArgs 0

#guard stackArgsFacts.outArgs == 2 && (FrameLayout.produce stackArgsFacts).check stackArgsFacts
#guard !({ FrameLayout.produce stackArgsFacts with outArgs := 1 } : FrameLayout).check stackArgsFacts
-- The callee reads its two incoming cells.
#guard (factsOf stackArgs 1).inArgs == 2 && (factsOf stackArgs 1).inArgsUsed == 2

-- Frameless leaves and small leaf frames skip the stack check; a leaf
-- frame beyond the slack and any frame with a call are checked.
#guard (FrameLayout.produce (factsOf leaf 0)).size == 0
#guard !FrameLayout.checked (factsOf leaf 0) (FrameLayout.produce (factsOf leaf 0))
#guard !FrameLayout.checked (factsOf slots 0) (FrameLayout.produce (factsOf slots 0))
#guard FrameLayout.checked (factsOf bigFrame 0) (FrameLayout.produce (factsOf bigFrame 0))
#guard FrameLayout.checked (factsOf deep 1) (FrameLayout.produce (factsOf deep 1))

/-! ## What stacking emits -/

def stacked (p : LProgram) : Option Stacked :=
  match Stacking.run p (Stacking.produce p) with
  | .ok s => some s
  | .error _ => none

def blockAt (s : Stacked) (i : Nat) : X86.Block := s.program.blocks[i]!

-- The exit group: `fail₁ … fail₄` set `eax` and jump to `failExit`, which
-- unwinds to `entrySp`, zeroes `edx` and runs the wrapper's epilogue.
def failBlock (k : Nat) : X86.Block :=
  { instructions := #[X86.Instr.mov .w32 .rax (.imm (UInt64.ofNat (k + 1)))], terminator := .jump 4 }

#guard (stacked leaf).any fun s =>
  (List.range 4).all (fun k => blockAt s k == failBlock k) &&
  (blockAt s 4).instructions.toList.take 2 == [.unwind entrySpCell, X86.Instr.alu .xor .w32 .rdx (.reg .rdx)] &&
  (blockAt s 4).terminator == .ret

-- `leaf` takes two `Nat`s: its wrapper checks them (a branch to `fail₃`)
-- before tagging them into `rdi`, `rsi` and calling the function.
#guard (stacked leaf).any fun s =>
  s.exports == [{ fn := 0, symbol := "t_leaf", block := 5 }] && s.program.entry == 5 &&
  (match (blockAt s 5).terminator with
    | .branch _ _ .signedLt 2 6 => true
    | _ => false) &&
  (blockAt s 6).instructions.toList.contains (.call 7)

-- A frameless leaf's block is its body and `ret`, with no prologue.
#guard (stacked leaf).any fun s =>
  blockAt s 7 == { instructions := #[X86.Instr.mov .w64 .rax (.reg .rdi),
    .op addMR [.reg .rax, .reg .rsi]], terminator := .ret }

-- `calls` checks the stack, allocates its frame and saves `rbx`; each
-- return restores `rbx` and frees the frame.
#guard (stacked calls).any fun s =>
  let check := blockAt s 7
  let body := blockAt s 8
  check.instructions == #[X86.Instr.lea .r11 (rspBelow (24 + slack))] &&
  (match check.terminator with
    | .branch _ [.reg .r11, .mem m] .unsignedLt 1 8 => m == stackLimitCell
    | _ => false) &&
  body.instructions.toList.take 2 == [subRsp 24, X86.Instr.store .w64 (rspAt 8) .rbx] &&
  body.instructions.toList.reverse.take 2 == [addRsp 24, X86.Instr.load .w64 .rbx (rspAt 8)] &&
  body.terminator == .ret

-- A tail call is the epilogue and a jump to the callee's entry.
#guard (stacked countdown).any fun s =>
  s.program.blocks.toList.any fun b =>
    b.terminator == .tailCall 8 && b.instructions.toList.getLast? == some (addRsp 72)

-- `fail` and `trap` jump to their exit-group block.
#guard (stacked deep).any fun s =>
  [(1 : UInt32), 3, 4].all fun k => s.program.blocks.toList.any (·.terminator == .jump (k - 1))

/-! ## What stacking rejects -/

def one (body : Array (Inst Loc)) (term : Term Loc := .ret [r .rax]) (more : Array (Block Loc) := #[]) :
    LProgram :=
  exported "t_bad" [{ params := [r .rdi], results := 1, blocks := #[{ body, term }] ++ more }]

def rejects (p : LProgram) : Bool := (Stacking.run p (Stacking.produce p)).toOption.isNone

#guard !rejects (one #[.move (r .rax) (r .rdi)])
-- A move between stack cells; a reserved register; an edge with arguments;
-- the entry block as a target; a tail call with stack arguments.
#guard rejects (one #[.move (s 0) (r .rdi), .move (s 1) (s 0), .move (r .rax) (s 1)])
#guard rejects (one #[.move (r .rax) (r .rbp)])
#guard rejects (one #[.move (r .rax) (r .rdi)] (.jmp ⟨1, [r .rax]⟩) #[{ term := .ret [r .rax] }])
#guard rejects (one #[.move (r .rax) (r .rdi)] (.jmp ⟨1, []⟩) #[{ term := .jmp ⟨0, []⟩ }])
#guard rejects ({ funcs := #[{ params := [r .rdi], results := 1, conv := .sysvExport "t", blocks := #[
    { term := .tail 1 ((List.range 8).map Xl.argLoc) }] }, sum9], main := 0 } : LProgram)
-- A tie whose definition is not its use's location; a cell in a register-only slot.
#guard rejects (one #[.op addMR [r .rax] [.r (r .rdi), .r (r .rdi)]])
#guard rejects (one #[.move (s 0) (r .rdi), .op (row .lea .w64 .RM) [r .rax] [.m { base := some (.r (s 0)) }]])
-- `main` must be an export, an export returns one value and takes at most five.
#guard rejects ({ funcs := #[{ params := [r .rdi], results := 1, blocks := #[{ term := .ret [r .rdi] }] }], main := 0 } : LProgram)
#guard rejects (exported "t" [{ params := [], results := 2, blocks := #[{ term := .ret [r .rax, r .rdx] }] }])
def sixParams : Func Loc := { params := (List.range 6).map Xl.paramLoc, results := 1, blocks := #[{ term := .ret [r .rdi] }] }

#guard rejects (exported "t" [sixParams])

-- Two exports sharing a symbol: `Backend.emit` (and so `Backend.compile`)
-- declines rather than dropping the second (the recheck path's
-- `stacking.symbols`); with symbols of their own both are exported.
def sharedSymbol : LProgram :=
  { twoExports with funcs := twoExports.funcs.modify 1 fun f => { f with conv := .sysvExport "t_add" } }

def emitted (p : LProgram) : Except Backend.Error Backend.Artifact :=
  Backend.emit p { provenance := .ixir1Policy (Compilatrix.Ixon.Address.replicate 0x42) 1 1 }

#guard (Stacking.run sharedSymbol (Stacking.produce sharedSymbol)).toOption.isSome
#guard match emitted sharedSymbol with | .error (.symbols "t_add") => true | _ => false
#guard match emitted twoExports with
  | .ok a => a.exports.map (·.1) == ["t_add", "t_twice"]
  | .error _ => false
#guard Backend.sharedSymbol? [⟨0, "a", 0⟩, ⟨1, "b", 1⟩, ⟨2, "a", 2⟩] == some "a"
#guard Backend.sharedSymbol? [⟨0, "a", 0⟩, ⟨1, "b", 1⟩] == none

-- Declared clobber sets (06 S15): `inc` changes `rcx` and `r11` besides its
-- result (its saved `rbx` does not count), so declaring `rax` alone is
-- rejected; a caller's declaration must cover its own stack check's `r11`
-- and what its callees may change.
def withClobbers (p : LProgram) (declared : Nat → List X86.GPR) : Bool :=
  (Stacking.run p (Stacking.produce p) (env := { clobbers := declared })).toOption.isSome

#guard withClobbers calls fun f => if f == 1 then [.rax, .rcx, .r11] else X86.SysV.callerSaved.toList
#guard !withClobbers calls fun f => if f == 1 then [.rax] else X86.SysV.callerSaved.toList
#guard !withClobbers calls fun f => if f == 0 then [.rax, .rdi] else X86.SysV.callerSaved.toList

/-! ## Tunnelling, order and linearisation -/

-- In `deep`, the recursion's failure branches are tunnelled straight to
-- the exit group's blocks.
#guard (stacked deep).any fun s =>
  let t := X86.Layout.tunnel s.program
  let targets := t.blocks.toList.flatMap fun b => match b.terminator with
    | .branch _ _ _ yes no _ => [yes, no]
    | _ => []
  [(0 : UInt32), 2].all targets.contains

def deepShape : Option (X86.Program × X86.Layout.Shape) :=
  (stacked deep).map fun s => (X86.Layout.tunnel s.program, s.shape)

#guard deepShape.any fun (p, sh) => X86.Layout.Order.check p sh (X86.Layout.Order.produce p sh)
-- The oracle drops the blocks tunnelling bypassed.
#guard deepShape.any fun (p, sh) => (X86.Layout.Order.produce p sh).flatten.length < p.blocks.size

def perturb (f : X86.Layout.Order → X86.Layout.Order) : Bool :=
  deepShape.any fun (p, sh) => !X86.Layout.Order.check p sh (f (X86.Layout.Order.produce p sh))

-- A duplicated block, a missing reachable block, the entry not first, a
-- block in another group's list, a group missing.
#guard perturb fun o => o.map fun g => g ++ g.take 1
#guard perturb fun o => o.map fun g => g.drop 1
#guard perturb fun o => o.map fun g => g.reverse
#guard perturb fun o => match o with
  | g₁ :: g₂ :: rest => (g₁ ++ g₂.take 1) :: g₂.drop 1 :: rest
  | o => o
#guard perturb fun o => o.drop 1

-- The order oracle is loop-aware: `loop`'s function (blocks 7–10: entry,
-- header, exit, body) is laid out entry, header, body, exit, after the
-- wrapper's two blocks, so the header (now block 3) branches out of the
-- loop to the exit (5) on the inverted condition and falls through to the
-- body (4).
def loopOrder : Option X86.Layout.Order := (stacked loop).map fun s =>
  X86.Layout.Order.produce (X86.Layout.tunnel s.program) s.shape

#guard loopOrder.any fun o => o[1]? == some [7, 8, 10, 9]
#guard (stacked loop).any fun s =>
  let t := X86.Layout.tunnel s.program
  match X86.Layout.run t s.shape (X86.Layout.Order.produce t s.shape) with
  | .ok (q, _) => match (q.blocks[3]!).terminator with
      | .branch _ _ .unsignedGe 5 4 .fall => true
      | _ => false
  | .error _ => false

-- Linearisation inverts a branch whose true target is next, and a branch
-- whose false target is next falls through to it (no `jmp`); otherwise
-- the false edge stays a `jmp rel32`.
def branchy : X86.Program := { entry := 0, blocks := #[
  { instructions := #[], terminator := .compare { width := .w64, left := .rdi, right := .imm 0 } .eq 1 2 },
  { instructions := #[], terminator := .ret },
  { instructions := #[], terminator := .ret },
  { instructions := #[], terminator := .ret }] }

#guard match ((X86.Layout.linearize branchy [0, 1, 2]).1.blocks[0]!).terminator with
  | .branch _ _ .ne 2 1 .fall => true
  | _ => false
#guard match ((X86.Layout.linearize branchy [0, 2, 1]).1.blocks[0]!).terminator with
  | .branch _ _ .eq 2 1 .fall => true
  | _ => false
#guard match ((X86.Layout.linearize branchy [0, 3, 1, 2]).1.blocks[0]!).terminator with
  | .branch _ _ .eq 2 3 .rel32 => true
  | _ => false

-- A fall-through branch encodes the producer and the `jcc` only: 5 bytes
-- fewer than with the `jmp rel32`.
def cmpRdi0 : X86.Compare := { width := .w64, left := .rdi, right := .imm 0 }

#guard X86.Stream.terminatorSize (.compare cmpRdi0 .eq 1 2) =
  X86.Stream.terminatorSize (.branch cmpRdi0.row.1 cmpRdi0.row.2 .eq 1 2 .fall) + 5
#guard (X86.Encode.encodeTerminator (.branch cmpRdi0.row.1 cmpRdi0.row.2 .eq 1 2 .fall)).fixups.size == 1

end CompilatrixTests.Backend.Cases
