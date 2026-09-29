import Compilatrix.Lir.WellFormed
import Compilatrix.Lir.SplitEdges
import Compilatrix.Lir.Operands
import CompilatrixTests.Lir.Region

/-!
# Hand-written Lir cases

Cheap assertions, checked while this module elaborates: word operations at
every width, memory and permissions, each `stuck` cause, `fail`/`trap`, the
clock at calls, tail calls and back edges, operand metadata, critical-edge
splitting on a loop, and one program per `WellFormed` violation.
-/

namespace CompilatrixTests.Lir.Cases

open Compilatrix Compilatrix.Lir

/-! ## Word operations -/

#guard BinOp.eval .shl .w8 1 20 == some 0
#guard BinOp.eval .shl .w64 1 65 == some 2
#guard BinOp.eval .shl .w32 1 33 == some 2
#guard BinOp.eval .shl .w16 0x8001 1 == some 2
#guard BinOp.eval .shr .w16 0xffff1234 4 == some 0x123
#guard BinOp.eval .shr .w64 0x8000000000000000 63 == some 1
#guard BinOp.eval .sar .w8 0x80 3 == some 0xf0
#guard BinOp.eval .sar .w8 0x80 20 == some 0xff
#guard BinOp.eval .sar .w32 0x7fffffff 31 == some 0
#guard BinOp.eval .sar .w64 0x8000000000000000 63 == some 0xffffffffffffffff
#guard BinOp.eval .udiv .w64 7 0 == none
#guard BinOp.eval .udiv .w8 0x107 0x102 == some 3
#guard BinOp.eval .urem .w8 7 0x100 == none
#guard BinOp.eval .urem .w64 0xffffffffffffffff 10 == some 5
#guard BinOp.eval .add .w32 0xffffffff 1 == some 0
#guard BinOp.eval .sub .w64 0 1 == some 0xffffffffffffffff
#guard BinOp.eval .sub .w8 0 1 == some 0xff
#guard BinOp.eval .mul .w16 0x100 0x100 == some 0
#guard BinOp.eval .xor .w64 0xff00 0x0ff0 == some 0xf0f0
#guard Cond.holds .slt .w8 0x80 0
#guard !Cond.holds .ult .w8 0x80 0
#guard Cond.holds .sge .w64 0 0x8000000000000000
#guard Cond.holds .eq .w32 0x100000005 5
#guard Cond.holds .tz .w8 0x100 0x1ff
#guard Cond.holds .tnz .w64 0x100 0x1ff
#guard Ovf.eval .addC 0xffffffffffffffff 1 == (0, true)
#guard Ovf.eval .addC 0x7fffffffffffffff 0x7fffffffffffffff == (0xfffffffffffffffe, false)
#guard Ovf.eval .subB 0 1 == (0xffffffffffffffff, true)
#guard Ovf.eval .subB 1 1 == (0, false)
#guard sext .w16 0x8000 == 0xffffffffffff8000
#guard sext .w32 0x7fffffff == 0x7fffffff
#guard dispWord (-8) == 0xfffffffffffffff8
#guard dispWord 2147483647 == 0x7fffffff

/-! ## Programs -/

private def v (x : VReg) : Arg := .v x
private def i (w : Word) : Arg := .imm w
private def to (l : Label) (args : List Arg := []) : Edge := ⟨l, args⟩

def single (blocks : Array Block) (params : List VReg := []) (results := 1) : Program :=
  { funcs := #[{ params, results, blocks }], main := 0 }

def run (p : Program) (args : List Word := []) (k := 100) : Outcome :=
  eval p k args (Region.initial 0) Region.ctx

def values : Outcome → Option (List Word)
  | .ok (vals, _) => some vals
  | _ => none

/-- Store 16 bits in a head, then load them sign- and zero-extended. -/
def memory : Program := single (results := 3) #[
  { body := #[.store .w16 { base := some .ctx, disp := 8 } (i 0x8001),
      .assign 0 (.load .w16 .sign { base := some .ctx, disp := 8 }),
      .assign 1 (.load .w8 .zero { base := some .ctx, disp := 9 }),
      .assign 2 (.load .w64 .zero { base := some .ctx, disp := Region.regionBaseOff })]
    term := .ret [v 0, v 1, v 2] }]

#guard values (run memory) == some [0xffffffffffff8001, 0x80, Region.heap]
#guard memory.wellFormed

/-- `[base + index·scale + disp]` with a negative displacement. -/
def indexed : Program := single (params := [0]) #[
  { body := #[.assign 1 (.load .w64 .zero { base := some .ctx, disp := Region.regionBaseOff }),
      .assign 2 (.addr { base := some (.v 1), index := some (0, .eight), disp := -16 }),
      .assign 3 (.bin .sub .w64 (v 2) (v 1))]
    term := .ret [v 3] }]

#guard values (run indexed [5]) == some [24]

-- Each `stuck` cause: division by zero, denied write, unmapped read,
-- undefined register, call arity mismatch.
def divide : Program := single (params := [0])
  #[{ body := #[.assign 1 (.bin .udiv .w64 (i 1) (v 0))], term := .ret [v 1] }]

def readOnly : Program := single (results := 0)
  #[{ body := #[.store .w8 { base := some .ctx, disp := 0x800 - 64 } (i 0)], term := .ret [] }]

def unmapped : Program := single #[{ body := #[.assign 0 (.load .w8 .zero { disp := 0x10 })], term := .ret [v 0] }]

def mismatch : Program :=
  { funcs := #[{ params := [], results := 0, blocks := #[{ body := #[.call [] 1 []], term := .ret [] }] },
      { params := [0], results := 0, blocks := #[{ term := .ret [] }] }]
    main := 0 }

#guard run divide [0] matches .stuck
#guard values (run divide [0x10]) == some [0]
#guard run readOnly matches .stuck
#guard run unmapped matches .stuck
#guard run (single #[{ term := .ret [v 7] }]) matches .stuck
#guard run mismatch matches .stuck
#guard run (single #[{ term := .fail .heap }]) matches .resource .heap
#guard run (single #[{ term := .trap }]) matches .trap

/-- `brOvf`'s result is bound on both edges and readable by their arguments. -/
def overflow : Program := single (params := [0, 1]) #[
  { term := .brOvf .addC 2 (v 0) (v 1) (to 1 [v 2, i 0]) (to 2 [v 2, i 1]) },
  { params := [3, 4], term := .ret [v 4] },
  { params := [5, 6], term := .ret [v 5] }]

#guard values (run overflow [1, 2]) == some [0]
#guard values (run overflow [0xffffffffffffffff, 2]) == some [1]
#guard overflow.wellFormed

/-- `count n`: a loop of `n` back edges, so `n` charges. -/
def count : Program := single (params := [0]) #[
  { term := .jump (to 1 [i 0]) },
  { params := [1], term := .br .ult .w64 (v 1) (v 0) (to 2) (to 3) },
  { body := #[.assign 2 (.bin .add .w64 (v 1) (i 1))], term := .jump (to 1 [v 2]) },
  { term := .ret [v 1] }]

#guard values (run count [10] 10) == some [10]
#guard run count [10] 9 matches .timeout
#guard count.wellFormed

/-- `down n`: self tail calls, one charge each. -/
def down : Program := single (params := [0]) #[
  { term := .br .eq .w64 (v 0) (i 0) (to 1) (to 2) },
  { term := .ret [i 42] },
  { body := #[.assign 1 (.bin .sub .w64 (v 0) (i 1))], term := .tail 0 [v 1] }]

#guard values (run down [5] 5) == some [42]
#guard run down [5] 4 matches .timeout

/-- Calls charge; returns do not. -/
def twice : Program :=
  { funcs := #[
      { params := [0], results := 1, blocks := #[
          { body := #[.call [1] 1 [v 0], .call [2] 1 [v 1]], term := .ret [v 2] }] },
      { params := [0], results := 1, blocks := #[
          { body := #[.assign 1 (.bin .mul .w64 (v 0) (i 3))], term := .ret [v 1] }] }]
    main := 0 }

#guard values (run twice [7] 2) == some [63]
#guard run twice [7] 1 matches .timeout
#guard twice.wellFormed

/-! ## Operands -/

#guard (Stmt.call [5, 6] 1 [v 1, i 3, v 2]).operands ==
  [⟨1, .use, .early, .fixed .rdi⟩, ⟨2, .use, .early, .fixed .rdx⟩,
    ⟨5, .define, .late, .fixed .rax⟩, ⟨6, .define, .late, .fixed .rdx⟩]
#guard (Stmt.assign 3 (.load .w8 .sign { base := some (.v 1), index := some (2, .four) })).operands ==
  [⟨1, .use, .early, .any⟩, ⟨2, .use, .early, .any⟩, ⟨3, .define, .late, .any⟩]
#guard (Term.tail 0 [v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8]).operands.getLast? ==
  some ⟨8, .use, .early, .stack⟩
#guard (Term.brOvf .subB 4 (v 1) (i 2) (to 1 [v 4]) (to 2)).operands ==
  [⟨1, .use, .early, .any⟩, ⟨4, .define, .late, .any⟩]

/-! ## Critical-edge splitting -/

/-- A loop whose latch returns to the header along two critical edges. -/
def latch : Program := single (params := [0]) #[
  { term := .jump (to 1 [i 0]) },
  { params := [1], term := .br .ult .w64 (v 1) (v 0) (to 2) (to 3) },
  { body := #[.assign 2 (.bin .add .w64 (v 1) (i 1)), .assign 3 (.bin .add .w64 (v 1) (i 2))]
    term := .br .tz .w64 (v 1) (i 1) (to 1 [v 2]) (to 1 [v 3]) },
  { term := .ret [v 1] }]

#guard latch.funcs[0]!.criticalEdges == [(2, 0), (2, 1)]
#guard !latch.wellFormed
#guard latch.splitCriticalEdges.wellFormed
#guard latch.splitCriticalEdges.funcs[0]!.blocks.size == 6
#guard latch.splitCriticalEdges.funcs[0]!.blocks[3]!.term == .jump (to 1 [v 2])
#guard (List.range 12).all fun k =>
  (values (run latch [9] k), (run latch [9] k) matches .timeout) ==
    (values (run latch.splitCriticalEdges [9] k), (run latch.splitCriticalEdges [9] k) matches .timeout)
#guard count.splitCriticalEdges == count

/-! ## `WellFormed` violations -/

def rejects (p : Program) (part : String) : Bool :=
  match p.check with
  | .ok () => false
  | .error e => (e.splitOn part).length > 1

#guard rejects { funcs := #[], main := 0 } "main function"
#guard rejects (single #[{ params := [0], term := .ret [v 0] }]) "entry block has parameters"
#guard rejects (single #[{ term := .jump (to 1) }, { term := .jump (to 0) }]) "edge to the entry block"
#guard rejects (single #[{ term := .jump (to 5) }]) "missing block"
#guard rejects (single #[{ term := .jump (to 1 [i 1]) }, { term := .ret [i 0] }]) "passes 1 arguments"
#guard rejects latch "critical edge"
#guard rejects (single #[{ term := .ret [] }]) "returns 0 values of 1"
#guard rejects (single #[{ body := #[.call [] 3 []], term := .ret [i 0] }]) "missing function"
#guard rejects (single (params := [0]) #[{ body := #[.call [1] 0 []], term := .ret [i 0] }])
  "passes 0 arguments for 1"
#guard rejects (single (params := [0]) #[{ body := #[.call [] 0 [v 0]], term := .ret [i 0] }]) "binds 0 results"
#guard rejects (single #[{ body := #[.assign 0 (.load .w8 .zero { disp := 2 ^ 31 })], term := .ret [v 0] }])
  "does not fit i32"
#guard !rejects (single #[{ body := #[.assign 0 (.load .w8 .zero { disp := -(2 ^ 31) })], term := .ret [v 0] }])
  "does not fit i32"
def ctxStore (w : Width) (m : Addr) : Program :=
  single (params := [0]) (results := 0) #[{ body := #[.store w m (i 0)], term := .ret [] }]

#guard rejects (ctxStore .w64 { base := some .ctx, disp := -64 }) "entrySp or stackLimit"
#guard rejects (ctxStore .w64 { base := some .ctx, disp := -56 }) "entrySp or stackLimit"
#guard rejects (ctxStore .w8 { base := some .ctx, disp := -49 }) "entrySp or stackLimit"
#guard rejects (ctxStore .w16 { base := some .ctx, disp := -65 }) "entrySp or stackLimit"
#guard rejects (ctxStore .w64 { base := some .ctx, index := some (0, .eight), disp := -100 })
  "entrySp or stackLimit"
#guard (ctxStore .w64 { base := some .ctx, disp := -72 }).wellFormed
#guard (ctxStore .w64 { base := some .ctx, disp := -48 }).wellFormed
#guard (ctxStore .w64 { base := some .ctx, index := some (0, .eight), disp := 8 }).wellFormed
#guard (ctxStore .w64 { base := some (.v 0), disp := -64 }).wellFormed
#guard rejects (single #[{ term := .ret [i 0] }, { term := .ret [i 1] }]) "unreachable blocks [1]"
#guard rejects (single #[{ term := .ret [v 3] }]) "v3 is used but never defined"
#guard rejects (single (params := [0]) #[{ body := #[.assign 0 (.arg (i 1))], term := .ret [v 0] }])
  "v0 is defined twice"
#guard rejects (single #[{ body := #[.assign 0 (.arg (v 0))], term := .ret [v 0] }]) "does not dominate"
-- A definition in one arm of a diamond does not reach the join.
#guard rejects (single (params := [0]) #[
  { term := .br .eq .w64 (v 0) (i 0) (to 1) (to 2) },
  { body := #[.assign 1 (.arg (i 1))], term := .jump (to 3) },
  { term := .jump (to 3) },
  { term := .ret [v 1] }]) "does not dominate"
-- `brOvf` may not read its own result as an operand.
#guard rejects (single #[{ term := .brOvf .addC 0 (v 0) (i 1) (to 1) (to 2) },
  { term := .ret [i 0] }, { term := .ret [i 1] }]) "does not dominate"
#guard rejects (single #[{ term := .tail 1 [] }] (results := 1)) "missing function"

end CompilatrixTests.Lir.Cases
