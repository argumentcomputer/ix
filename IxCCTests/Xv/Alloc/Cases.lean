import IxCCTests.Xv.Alloc.Support
import IxCCTests.Support.Rng

/-!
# Hand-written allocation cases

Cheap assertions, checked while this module elaborates:

- the validator's `NatMap` (keys through every traversal), sorted register
  sets and the abstract state's transfer functions (`bindParams`, `define`,
  `stepMove`, outgoing cells at calls);
- the parallel-move resolver against the parallel meaning of its input,
  with and without free registers (the extra slot and the borrowed victim);
- each validator check on synthetic instructions, including the forms no
  selected program has yet (late uses, stack arguments, results past two);
- calls: caller-saved registers erased, a runtime procedure's smaller
  clobber set honoured, outgoing cells released;
- stack parameters and arguments (nine of each) through linear scan and all
  slots, run at Xl against Xv.
-/

namespace IxCCTests.Xv.Alloc.Cases

open IxCC IxCC.Lir IxCC.Xv IxCCTests.Lir IxCCTests.Support
open IxCC.Xv.Validate (NatMap AState VSet Code)
open IxCC.Xv.Alloc (Edit Output BlockOut)

/-! ## `NatMap` -/

def keys : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 18, 19, 20, 31, 32, 33, 63, 64, 100, 255, 256, 1000]

def sample : NatMap Nat := NatMap.ofList (keys.map fun k => (k, 2 * k))

#guard keys.all fun k => sample.find? k == some (2 * k)
#guard (List.range 1001).all fun k => (sample.find? k).isSome == keys.contains k
#guard sample.size == keys.length
/- Traversals see the right keys. -/
#guard sample.all fun k v => v == 2 * k
#guard (sample.toList.map (·.1)).mergeSort == keys
#guard (sample.filterMap fun k v => if k % 3 == 0 then some (k + v) else none).toList.all fun (k, v) => v == 3 * k && k % 3 == 0
#guard ((sample.filterMap fun k v => if k % 3 == 0 then some v else none).toList.map (·.1)).mergeSort ==
  keys.filter (· % 3 == 0)
/- Erasing prunes back to the empty trie. -/
#guard keys.foldl (fun m k => m.erase k) sample == NatMap.leaf
#guard ((keys.foldl (fun m k => if k % 2 == 0 then m.erase k else m) sample).toList.map (·.1)).mergeSort ==
  keys.filter (· % 2 == 1)

/-! ## Sets and states -/

#guard VSet.ofList [5, 3, 9, 3, 1] == [1, 3, 5, 9]
#guard VSet.erase 5 [1, 3, 5, 9] == [1, 3, 9]
#guard VSet.subset [3, 9] [1, 3, 5, 9] && !VSet.subset [2] [1, 3]

def rax : Loc := .reg .rax
def rcx : Loc := .reg .rcx
def rdx : Loc := .reg .rdx
def rbx : Loc := .reg .rbx

/-- `rax ↦ {3}`, `rcx ↦ {8}`, `slot 0 ↦ {1, 3}`. -/
def st0 : AState := AState.ofList [(rax, [3]), (rcx, [8]), (.slot 0, [3, 1])]

/- Binding parameters `[2, 3] := [3, 8]` (a loop rotating `3` into `2`). -/
#guard (st0.bindParams [2, 3] [3, 8]).get rax == [2]
#guard (st0.bindParams [2, 3] [3, 8]).get rcx == [3, 8]
#guard (st0.bindParams [2, 3] [3, 8]).get (.slot 0) == [1, 2]
/- A definition forgets its register everywhere. -/
#guard (st0.define [(3, rdx)] []).get (.slot 0) == [1] && (st0.define [(3, rdx)] []).get rax == []
#guard (st0.define [(3, rdx)] [rcx]).get rcx == [] && (st0.define [(3, rdx)] []).get rdx == [3]
/- A move copies facts; from nothing known it erases the destination (gap 1). -/
#guard (st0.stepMove rbx rax).get rbx == [3] && (st0.stepMove rax rbx).get rax == []
/- A call releases outgoing cells. -/
#guard ((st0.set (.outArg 2) [7]).clearOutArgs).get (.outArg 2) == [] &&
  ((st0.set (.outArg 2) [7]).clearOutArgs).get (.slot 0) == [1, 3]
#guard st0.le (st0.set rdx [4]) && !(st0.set rdx [4]).le st0

/-! ## Parallel moves -/

def locsPool : Array Loc := #[rax, rcx, rdx, rbx, .reg .rsi, .reg .rdi, .slot 0, .slot 1, .slot 2, .slot 3]

/-- A random parallel move with distinct destinations over `locsPool`. -/
def randomMoves (seed : UInt64) : Array (Loc × Loc) := Id.run do
  let mut rng := Rng.ofSeed seed
  let (n, r) := (RngM.range 1 8).run rng
  rng := r
  let mut moves := #[]
  for _ in [:n] do
    let (d, r) := (RngM.pick locsPool).run rng
    let (s, r) := (RngM.pick locsPool).run r
    rng := r
    if !moves.any (·.1 == d) then moves := moves.push (d, s)
  return moves

/-- The resolved edits have the parallel meaning on every location except
the free registers and the extra slots, restore the victim, and never move
cell to cell. -/
def resolves (seed : UInt64) (free : List X86.GPR) : Bool :=
  let moves := randomMoves seed
  let sc : IxCC.Xv.Alloc.ParMove.Scratch :=
    { free, cycleSlot := .slot 90, victim := .r11, saveSlot := .slot 91 }
  let (edits, _) := IxCC.Xv.Alloc.ParMove.resolve moves sc
  let init (l : Loc) : Option Nat := some (Validate.locKey l)
  let par := IxCC.Xv.Alloc.ParMove.runParallel moves.toList init
  let seq := IxCC.Xv.Alloc.ParMove.runSequential edits.toList init
  let watched := (locsPool.toList ++ [Loc.reg .r11]).filter fun (l : Loc) => match l with
    | Loc.reg r => !free.contains r
    | _ => true
  watched.all (fun l => par l == seq l) && edits.all fun | .move d s => !(d.isCell && s.isCell)

#guard (List.range 300).all fun i => resolves (UInt64.ofNat i) [.r8, .r9]
#guard (List.range 300).all fun i => resolves (UInt64.ofNat i) [.r8]
#guard (List.range 300).all fun i => resolves (UInt64.ofNat i) []

/-! ## The validator's checks on synthetic instructions -/

def ctx : Validate.Ctx := { env := {}, numSlots := 2, stackParams := 0 }

def use (v : VReg) (con : Con := .any) (pos : Pos := .early) : Operand VReg := ⟨v, .use, pos, con⟩
def dfn (v : VReg) (con : Con := .any) (pos : Pos := .late) : Operand VReg := ⟨v, .define, pos, con⟩

def codeOf (a : AState) (ops : List (Operand VReg)) (ls : List Loc) : Option Code :=
  match Validate.stepOperands ctx a ops ls true with
  | .ok _ => none
  | .error c => some c

def st1 : AState := AState.ofList [(rax, [1]), (rcx, [2]), (.slot 0, [1])]

#guard codeOf st1 [use 1, use 2, dfn 3] [rax, rcx, rax] == none
/- Gap 3: a late use is checked, and may not share a definition's location. -/
#guard codeOf st1 [use 1 .reg, use 2 .reg .late, dfn 3 (.reuse 0)] [rax, rcx, rax] == none
#guard codeOf st1 [use 1 .reg, use 1 .reg .late, dfn 3 (.reuse 0)] [rax, rax, rax] == some .alias
#guard codeOf st1 [use 1 .reg, use 2 .reg .late, dfn 3 (.reuse 0)] [rax, rdx, rax] == some .useMissing
/- Gap 4: an early definition may not sit on a use. -/
#guard codeOf st1 [use 1, dfn 3 .reg .early] [rax, rax] == some .alias
#guard codeOf st1 [use 1, dfn 3 .reg .early] [rax, rdx] == none
/- Gap 5: reserved registers, also when fixed. -/
#guard codeOf st1 [use 1, dfn 3] [rax, .reg .rsp] == some .reserved
#guard codeOf st1 [use 1 (.fixed .r15)] [.reg .r15] == some .reserved
#guard codeOf st1 [dfn 3 .any] [.reg .rbp] == some .reserved
/- Constraints and ties. -/
#guard codeOf st1 [use 1 .reg] [.slot 0] == some .constraint
#guard codeOf st1 [use 1 (.fixed .rcx)] [rax] == some .constraint
#guard codeOf st1 [dfn 3 .stack] [rax] == some .constraint
#guard codeOf st1 [use 1 .reg, dfn 3 (.reuse 0)] [rax, rcx] == some .tie
#guard codeOf st1 [use 1 .reg .late, dfn 3 (.reuse 0)] [rax, rax] == some .tie
/- Slots in range; outgoing cells only in argument setup. -/
#guard codeOf st1 [dfn 3] [.slot 2] == some .cellRange
#guard codeOf st1 [dfn 3] [.outArg 0] == some .cellRange
#guard codeOf st1 [dfn 3, dfn 4] [rdx, rdx] == some .alias
/- One register defined twice: Xv keeps the last value, so this is refused. -/
#guard codeOf st1 [dfn 3, dfn 3] [rdx, rbx] == some .alias
#guard codeOf st1 [use 1, dfn 3] [.slot 0, .slot 1] == none

/-! ## Calls, clobbers and whole functions -/

def addMR : X86.Op := Select.row .add .w64 .MR

/-- `f1(x) = x + x`. -/
def double : Func VReg := { params := [0], results := 1, blocks := #[
  { body := #[.op addMR [1] [.r 0, .r 0]], term := .ret [1] }] }

/-- `main(a) = f1(a) + a`: `a` lives across the call. -/
def caller : Func VReg := { params := [0], results := 1, blocks := #[
  { body := #[.call 1 [0] [1], .op addMR [2] [.r 1, .r 0]], term := .ret [2] }] }

def prog : VProgram := { funcs := #[caller, double], main := 0 }

/-- `a` kept in `reg` across the call (moved from `rdi` before it). -/
def keepIn (reg : X86.GPR) : Output :=
  { numSlots := 0, blocks := [
    { cert := [(.reg .rdi, [0])]
      edits := [(0, .move (.reg reg) (.reg .rdi))]
      locs := [[.reg .rdi, .reg .rax], [.reg .rax, .reg reg, .reg .rax]]
      termLocs := [.reg .rax] }] }

def verdict (env : Xl.Env) (o : Output) : Option Code :=
  match Validate.func env 0 caller o with
  | .ok () => none
  | .error e => some e.code

/- Callee-saved survives; caller-saved does not, unless the callee declares
a clobber set without it (a runtime procedure, 04 §7). -/
#guard verdict {} (keepIn .rbx) == none
#guard verdict {} (keepIn .rcx) == some .useMissing
#guard verdict { clobbers := fun _ => [.rax, .rdx] } (keepIn .rcx) == none
/- The convention: arguments and results exactly where it puts them. -/
#guard verdict {} { keepIn .rbx with blocks := [{ (keepIn .rbx).blocks[0]! with
    locs := [[.reg .rsi, .reg .rax], [.reg .rax, .reg .rbx, .reg .rax]] }] } == some .convention
/- A call binding one register to both results. -/
def dupRets : Func VReg := { params := [0], results := 1, blocks := #[
  { body := #[.call 1 [0] [1, 1]], term := .ret [1] }] }
#guard match Validate.func {} 0 dupRets { numSlots := 0, blocks := [
    { cert := [(.reg .rdi, [0])], locs := [[.reg .rdi, .reg .rax, .reg .rdx]], termLocs := [.reg .rax] }] } with
  | .error e => e.code == .alias
  | .ok () => false
/- Gap 2: block 0's certificate is checked against the entry convention. -/
#guard verdict {} { keepIn .rbx with blocks := [{ (keepIn .rbx).blocks[0]! with cert := [(.reg .rsi, [0])] }] } ==
  some .entry
/- Gap 1 made strict: a move from a location holding nothing known. -/
#guard verdict {} { keepIn .rbx with blocks := [{ (keepIn .rbx).blocks[0]! with
    edits := [(0, .move (.reg .rbx) (.reg .rdi)), (1, .move (.reg .rbx) (.slot 0))] }], numSlots := 1 } ==
  some .unknownSource
/- Edits after the terminator are refused (gap 7), as are out-of-order ones. -/
#guard verdict {} { keepIn .rbx with blocks := [{ (keepIn .rbx).blocks[0]! with
    edits := [(0, .move (.reg .rbx) (.reg .rdi)), (3, .move (.reg .rbx) (.reg .rax))] }] } == some .editOrder

/-- The allocations the allocator makes of `prog` run like it. -/
def runsLike (env : Xl.Env) (outs : List Output) (args : List Word) : Bool :=
  match IxCC.Xv.Alloc.applyProgram prog outs with
  | .ok g => (differential prog g env args 0).toBool
  | .error _ => false

#guard runsLike {} [keepIn .rbx, (IxCC.Xv.Alloc.LinearScan.run {} double).toOption.get!] [21]
#guard match IxCC.Xv.Alloc.run {} prog with
  | .ok r => (differential prog r.program {} [21] 0).toBool
  | .error _ => false

/-! ## Stack parameters and arguments -/

/-- `nine(p0 … p8) = p0 + p8` (two parameters in incoming cells). -/
def nine : Func VReg := { params := List.range 9, results := 1, blocks := #[
  { body := #[.op addMR [9] [.r 0, .r 8]], term := .ret [9] }] }

/-- `main(a) = nine(a, 1, …, a)`, with `a` live across the call. -/
def callNine : Func VReg := { params := [0], results := 1, blocks := #[
  { body := ((List.range 7).map fun j => Inst.op (Select.row .mov .w32 .OI) [j + 1] [.i (UInt64.ofNat j)]).toArray ++
      #[.call 1 ([0] ++ (List.range 7).map (· + 1) ++ [0]) [8], .op addMR [9] [.r 8, .r 0]]
    term := .ret [9] }] }

def stackProg : VProgram := { funcs := #[callNine, nine], main := 0 }

#guard match IxCC.Xv.Alloc.run {} stackProg with
  | .ok r => r.outcomes.all (fun | .scan => true | _ => false) && (differential stackProg r.program {} [5] 0).toBool
  | .error _ => false
#guard match IxCC.Xv.Alloc.runAllSlots {} stackProg with
  | .ok r => (differential stackProg r.program {} [5] 0).toBool
  | .error _ => false
#guard match IxCC.Xv.Alloc.run {} stackProg (IxCC.Xv.Alloc.Chaos.ofSeed 7) with
  | .ok r => (differential stackProg r.program {} [5] 0).toBool
  | .error _ => false

/-- `eight(p0 … p7) = p0 + p7`. -/
def eight : Func VReg := { params := List.range 8, results := 1, blocks := #[
  { body := #[.op addMR [8] [.r 0, .r 7]], term := .ret [8] }] }

/-- A tail call with eight arguments has no allocation (05 §13 Q7): both
allocators decline it, and the validator rejects a hand-made one. -/
def tailEight : Func VReg := { params := List.range 8, results := 1, blocks := #[
  { term := .tail 1 (List.range 8) }] }

#guard (IxCC.Xv.Alloc.run {} { funcs := #[tailEight, eight], main := 0 }).toBool == false
#guard match Validate.func {} 0 tailEight
    { numSlots := 0, blocks := [{ cert := [], termLocs := (List.range 8).map Xl.argLoc }] } with
  | .error e => e.code == .convention
  | .ok () => false
/- Three results: past the two result registers (05 §6). -/
def threeResults : Func VReg := { params := [0], results := 1, blocks := #[
  { body := #[.call 1 [0] [1, 2, 3]], term := .ret [1] }] }
#guard (IxCC.Xv.Alloc.LinearScan.run {} threeResults).toBool == false
#guard (IxCC.Xv.Alloc.AllSlots.run threeResults).toBool == false

end IxCCTests.Xv.Alloc.Cases
