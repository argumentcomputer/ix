import CompilatrixTests.Xv.Support
import CompilatrixTests.Lir.Props

/-!
# Hand-written selection cases

Cheap assertions, checked while this module elaborates. Each rule gets its
edge values: the form selection picks at the imm8, imm32 and displacement
boundaries, and agreement of `Lir.eval` with `Xv.eval` there (outcome,
values, heap and context words). Also: the overflow boundary of rule 4,
load sinking blocked by a store, a call or a narrow load, the protected
context cells, narrow arithmetic, sign-extending loads, constant shifts,
the clock on a self-loop, `WellFormed` rejections and operand metadata.
-/

namespace CompilatrixTests.Xv.Cases

open Compilatrix Compilatrix.Lir Compilatrix.Xv CompilatrixTests.Lir CompilatrixTests.Xv

private def v (x : VReg) : Lir.Arg := .v x
private def i (w : Word) : Lir.Arg := .imm w
private def to (l : Label) (args : List Lir.Arg := []) : Lir.Edge := ⟨l, args⟩
private def bin (x : VReg) (o : BinOp) (w : Width) (a b : Lir.Arg) : Stmt := .assign x (.bin o w a b)

/-- A one-function program; `v0`, `v1` are parameters. -/
def single (blocks : Array Lir.Block) (params : List VReg := [0, 1]) (results := 1) : Lir.Program :=
  { funcs := #[{ params, results, blocks }], main := 0 }

/-- `x := rhs; ret x`, with `v0`, `v1` parameters. -/
def expr (body : Array Stmt) (x : VReg := 9) : Lir.Program :=
  single #[{ body, term := .ret [v x] }]

/-- The heap base (`Region.heap`) in `v5`. -/
def heapBase : Stmt := .assign 5 (.load .w64 .zero { base := some .ctx, disp := Region.regionBaseOff })

def two (a b : Word) : List Word := [a, b]

/-- The selected row of the last instruction of block 0. -/
def lastRow (p : Lir.Program) : Option X86.Op :=
  match (selected p).getLast? with
  | some (.op o ..) => some o
  | _ => none

def lastInst (p : Lir.Program) : Option (Inst VReg) := (selected p).getLast?

def jccRow (p : Lir.Program) (b : Label := 0) : Option (X86.Op × List (XArg VReg) × X86.Condition) :=
  match selectedTerm p b with
  | some (.jcc o args _ c ..) => some (o, args, c)
  | _ => none

/-! ## Rule 5: immediates -/

def immProg (k : Word) : Lir.Program := expr #[.assign 9 (.arg (i k))]

#guard lastInst (immProg 0) == some (.zero 9)
#guard lastRow (immProg 1) == some (Select.row .mov .w32 .OI)
#guard lastRow (immProg 0xffffffff) == some (Select.row .mov .w32 .OI)
#guard lastRow (immProg 0x100000000) == some (Select.row .mov .w64 .OI)
#guard lastRow (immProg 0xffffffffffffffff) == some (Select.row .mov .w64 .MI)
#guard lastRow (immProg 0xffffffff80000000) == some (Select.row .mov .w64 .MI)
#guard lastRow (immProg 0xffffffff7fffffff) == some (Select.row .mov .w64 .OI)
#guard lastRow (immProg 0x8000000000000000) == some (Select.row .mov .w64 .OI)
#guard [0, 1, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0xffffffffffffffff, 0xffffffff80000000,
    0xffffffff7fffffff, 0x8000000000000000].all fun k => agrees (immProg k) []

/-! ## Rule 6: `op r/m, imm8` and `imm32`, tied -/

def xorImm (w : Width) (k : Word) : Lir.Program := expr #[bin 9 .xor w (v 0) (i k)]

#guard lastRow (xorImm .w64 127) == some (Select.row .xor .w64 .MI8)
#guard lastRow (xorImm .w64 0xffffffffffffff80) == some (Select.row .xor .w64 .MI8)
#guard lastRow (xorImm .w64 128) == some (Select.row .xor .w64 .MI)
#guard lastRow (xorImm .w64 0xffffffffffffff7f) == some (Select.row .xor .w64 .MI)
#guard lastRow (xorImm .w64 0x7fffffff) == some (Select.row .xor .w64 .MI)
#guard lastRow (xorImm .w64 0xffffffff80000000) == some (Select.row .xor .w64 .MI)
#guard lastRow (xorImm .w64 0x80000000) == some (Select.row .xor .w64 .MR)
#guard lastRow (xorImm .w32 0xffffffff) == some (Select.row .xor .w32 .MI8)
#guard lastRow (xorImm .w32 0x80000000) == some (Select.row .xor .w32 .MI)
#guard lastRow (xorImm .w32 0x1ffffffff) == some (Select.row .xor .w32 .MI8)
def sweepAluImm (_ : Unit) : Bool :=
  [127, 128, 0xffffffffffffff80, 0xffffffffffffff7f, 0x7fffffff, 0x80000000, 0xffffffff80000000,
    0xffffffff7fffffff, 0x1ffffffff].all fun k =>
  [X86.Width.w8, .w16, .w32, .w64].all fun w =>
    [BinOp.add, .sub, .and, .or, .xor].all fun o =>
      agrees (expr #[bin 9 o w (v 0) (i k)]) (two 0x8000000080000080 3) &&
      agrees (expr #[bin 9 o w (i k) (v 0)]) (two 0xffffffffffffffff 3) &&
      agrees (expr #[bin 9 o w (i k) (i 0x80)]) []

/- The `x := a + b` tie: `a` single-use keeps the tied `add`. -/
#guard lastRow (expr #[bin 9 .add .w64 (v 0) (v 1)]) == some (Select.row .add .w64 .MR)

/-! ## Rule 7: `lea` for three-operand add -/

/-- `v0` lives on (it is returned too), so the add is an untied `lea`. -/
def leaProg (b : Lir.Arg) (o : BinOp := .add) : Lir.Program :=
  single (results := 2) #[{ body := #[bin 9 o .w64 (v 0) b], term := .ret [v 9, v 0] }]

#guard lastInst (leaProg (v 1)) == some (.op (Select.row .add .w64 .MR) [9] [.r 1, .r 0])
#guard lastRow (single (results := 3) #[{ body := #[bin 9 .add .w64 (v 0) (v 1)], term := .ret [v 9, v 0, v 1] }]) ==
  some Select.leaRow
#guard lastRow (leaProg (i 0x7fffffff)) == some Select.leaRow
#guard lastRow (leaProg (i 0x80000000)) == some (Select.row .add .w64 .MR)
#guard lastRow (leaProg (i 0xffffffff80000000)) == some Select.leaRow
#guard lastRow (leaProg (i 5) .sub) == some Select.leaRow
#guard lastRow (leaProg (i 0xffffffff80000000) .sub) == some (Select.row .sub .w64 .MI)
#guard lastRow (leaProg (i 0xffffffff7fffffff) .sub) == some (Select.row .sub .w64 .MR)
#guard [v 1, i 0x7fffffff, i 0x80000000, i 0xffffffff80000000, i 5].all fun b =>
  agrees (leaProg b) (two 0xfffffffffffffff0 0x20) && agrees (leaProg b .sub) (two 3 0x20)

/-! ## Rule 8: address folding -/

/-- `t := p + d₁; y := load [t + d₂]`, with `p` the heap base. -/
def foldProg (d₁ : Word) (d₂ : Int) : Lir.Program :=
  expr #[heapBase, bin 6 .add .w64 (v 5) (i d₁), .assign 9 (.load .w64 .zero { base := some (.v 6), disp := d₂ })]

def loadAmode (p : Lir.Program) : Option (Amode VReg) :=
  match lastInst p with
  | some (.op _ _ [.m a]) => some a
  | _ => none

#guard (loadAmode (foldProg 16 8)).map (·.disp.toInt) == some 24
#guard (loadAmode (foldProg 16 8)).map (·.base) == some (some (.r 5))
#guard fired (foldProg 16 8) "amode.fold"
/- The fold stops at the i32 boundary: `2^31 − 9 + 8` fits, `2^31 − 8 + 8` does not. -/
#guard (loadAmode (foldProg 0x7ffffff7 8)).map (·.disp.toInt) == some 0x7fffffff
#guard (loadAmode (foldProg 0x7ffffff8 8)).map (·.base) == some (some (.r 6))
#guard (loadAmode (foldProg 0xffffffff80000008 (-8))).map (·.disp.toInt) == some (-0x80000000)
#guard (loadAmode (foldProg 0xffffffff80000008 (-9))).map (·.base) == some (some (.r 6))
/- Wrapping: `p + (2^64 − 8) + 16 = p + 8`. -/
#guard (loadAmode (foldProg 0xfffffffffffffff8 16)).map (·.disp.toInt) == some 8

/-- A scaled index from `shl ≤ 3`, and a context field through `addr`. -/
def indexProg (s : Word) : Lir.Program :=
  expr #[heapBase, bin 6 .and .w64 (v 0) (i 7), bin 7 .shl .w64 (v 6) (i s),
    .assign 9 (.load .w64 .zero { base := some (.v 5), index := some (7, .one), disp := 16 })]

#guard (loadAmode (indexProg 3)).map (·.index) == some (some (6, .eight))
#guard (loadAmode (indexProg 4)).map (·.index) == some (some (7, .one))
#guard [0, 1, 2, 3, 4].all fun s => agrees (indexProg s) (two 5 0)

def ctxFieldProg : Lir.Program :=
  expr #[.assign 6 (.addr { base := some .ctx, disp := 8 }),
    .assign 9 (.load .w32 .zero { base := some (.v 6), disp := 4 })]

#guard loadAmode ctxFieldProg == some { base := some .ctx, disp := 12 }
#guard agrees ctxFieldProg (two 0 0)

/-- A store through `addr [ctx − 64]` does not fold into a protected context
store (which `WellFormed` would reject). -/
def protectedProg : Lir.Program :=
  expr #[.assign 6 (.addr { base := some .ctx, disp := -64 }), .store .w64 { base := some (.v 6) } (v 0),
    .assign 9 (.arg (i 0))]

#guard match select protectedProg with
  | .ok (q, _) => q.wellFormed && !fired protectedProg "amode.fold"
  | .error _ => false

/-! ## Rules 3 and 9: loads folded into their consumer -/

/-- `y := load w e [p + 8]`, an optional statement between, then
`br c w' y k`. -/
def cmpLoadProg (w : Width) (e : Ext) (w' : Width) (between : Array Stmt) (k : Lir.Arg := i 0x80) :
    Lir.Program :=
  single #[
    { body := #[heapBase, .store .w64 { base := some (.v 5), disp := 8 } (i 0xffffffffffffff80),
        .assign 6 (.load w e { base := some (.v 5), disp := 8 })] ++ between
      term := .br .eq w' (v 6) k (to 1) (to 2) },
    { term := .ret [i 1] }, { term := .ret [i 0] }]

#guard fired (cmpLoadProg .w64 .zero .w64 #[]) "load.sink"
#guard fired (cmpLoadProg .w32 .zero .w8 #[]) "load.sink"
/- A narrower load than the compare does not fold. -/
#guard !fired (cmpLoadProg .w8 .sign .w64 #[]) "load.sink"
#guard !fired (cmpLoadProg .w16 .zero .w32 #[]) "load.sink"
/-- A store in between (here to the loaded cell) blocks the fold. -/
def overwrite : Stmt := .store .w64 { base := some (.v 5), disp := 8 } (i 0x80)
#guard !fired (cmpLoadProg .w64 .zero .w64 #[overwrite]) "load.sink"
def sweepCmpLoad (_ : Unit) : Bool :=
  [X86.Width.w8, .w16, .w32, .w64].all fun w => [X86.Width.w8, .w16, .w32, .w64].all fun w' =>
  [Ext.zero, .sign].all fun e => [#[], #[overwrite], #[bin 7 .add .w64 (v 0) (v 1)]].all fun between =>
    [i 0x80, i 0xffffffffffffff80, v 1].all fun k =>
      agrees (cmpLoadProg w e w' between k) (two 0 0xffffffffffffff80)
/-- The load as the second operand: the condition is swapped. -/
def cmpLoadRight : Lir.Program :=
  single #[
    { body := #[heapBase, .assign 6 (.load .w64 .zero { base := some (.v 5) })]
      term := .br .ult .w64 (v 0) (v 6) (to 1) (to 2) },
    { term := .ret [i 1] }, { term := .ret [i 0] }]
#guard (jccRow cmpLoadRight).map (·.2.2) == some .unsignedGt
#guard [0, 1, 0x8000000000000000, 0xffffffffffffffff].all fun a => agrees cmpLoadRight (two a 0) (seed := a)

/-- `y := load w [p]; x := a * y` (rule 9). -/
def mulLoadProg (w : Width) (w' : Width) (between : Array Stmt) : Lir.Program :=
  expr (#[heapBase, .assign 6 (.load w .zero { base := some (.v 5) })] ++ between ++ #[bin 9 .mul w' (v 0) (v 6)])

#guard fired (mulLoadProg .w64 .w64 #[]) "imul.load"
#guard fired (mulLoadProg .w64 .w32 #[]) "imul.load"
#guard !fired (mulLoadProg .w32 .w64 #[]) "imul.load"
#guard !fired (mulLoadProg .w64 .w64 #[.store .w64 { base := some (.v 5) } (i 3)]) "imul.load"
#guard !fired (mulLoadProg .w64 .w64 #[.store .w8 { base := some (.v 5), disp := 100 } (v 0)]) "imul.load"
def sweepMulLoad (_ : Unit) : Bool :=
  [X86.Width.w8, .w16, .w32, .w64].all fun w => [X86.Width.w8, .w16, .w32, .w64].all fun w' =>
  [#[], #[.store .w64 { base := some (.v 5) } (v 1)]].all fun between =>
    agrees (mulLoadProg w w' between) (two 0x123456789 0xfedcba987) (seed := 7)

/-! ## Rule 1: compare and branch -/

def brProg (c : Cond) (w : Width) (a b : Lir.Arg) : Lir.Program :=
  single #[{ term := .br c w a b (to 1) (to 2) }, { term := .ret [i 1] }, { term := .ret [i 0] }]

#guard (jccRow (brProg .eq .w64 (v 0) (i 127))).map (·.1) == some (Select.row .cmp .w64 .MI8)
#guard (jccRow (brProg .eq .w64 (v 0) (i 128))).map (·.1) == some (Select.row .cmp .w64 .MI)
#guard (jccRow (brProg .eq .w64 (v 0) (i 0x80000000))).map (·.1) == some (Select.row .cmp .w64 .MR)
#guard (jccRow (brProg .eq .w8 (v 0) (i 0x80))).map (·.1) == some (Select.row .cmp .w8 .MI)
#guard (jccRow (brProg .eq .w16 (v 0) (i 0xff80))).map (·.1) == some (Select.row .cmp .w16 .MI8)
/- An immediate on the left swaps the condition. -/
#guard (jccRow (brProg .ult .w64 (i 5) (v 0))).map (·.2.2) == some .unsignedGt
#guard (jccRow (brProg .sle .w32 (i 5) (v 0))).map (·.2.2) == some .signedGe
def edgeWords : List Word :=
  [0, 1, 0x7f, 0x80, 0xff, 0x7fff, 0x8000, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000,
    0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff]
def sweepBranch (_ : Unit) : Bool :=
  [Cond.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge, .tz, .tnz].all fun c =>
  [X86.Width.w8, .w16, .w32, .w64].all fun w => [0x80, 0xffffffff, 0x7fffffff].all fun k =>
    [0, 0x80, 0xffffffff80000000, 0x7fffffff, 0xffffffffffffffff].all fun a =>
      agrees (brProg c w (v 0) (i k)) (two a 0) && agrees (brProg c w (i k) (v 0)) (two a 0) &&
      agrees (brProg c w (v 0) (v 1)) (two a k) && agrees (brProg c w (i a) (i k)) []

/-! ## Rule 2: tag tests by `and` -/

#guard (jccRow (brProg .tz .w8 (v 0) (i 1))).map (fun (o, _, c) => (o, c)) == some (Select.row .and .w8 .MI, .eq)
#guard (jccRow (brProg .tnz .w64 (v 0) (v 1))).map (fun (o, _, c) => (o, c)) ==
  some (Select.row .and .w64 .MR, .ne)
#guard agrees (brProg .tz .w8 (v 0) (i 0x1ff)) (two 0x100 0)
#guard agrees (brProg .tnz .w32 (v 0) (v 1)) (two 0x100000000 0x100000001)

/-! ## Rule 4: overflow branches -/

def ovfProg (o : Ovf) (a b : Lir.Arg) : Lir.Program :=
  single #[{ term := .brOvf o 9 a b (to 1) (to 2) }, { term := .ret [v 9] }, { term := .fail .natOverflow }]

#guard (jccRow (ovfProg .addC (v 0) (v 1))).map (fun (o, _, c) => (o, c)) ==
  some (Select.row .add .w64 .MR, .unsignedLt)
#guard (jccRow (ovfProg .subB (v 0) (i 1))).map (·.1) == some (Select.row .sub .w64 .MI8)
#guard (jccRow (ovfProg .addC (v 0) (i 0x80000000))).map (·.1) == some (Select.row .add .w64 .MR)
/- The carry and borrow boundaries. -/
def sweepOverflow (_ : Unit) : Bool :=
  [(0xffffffffffffffff, 1), (0xfffffffffffffffe, 1), (0x8000000000000000, 0x8000000000000000),
    (0x7fffffffffffffff, 0x8000000000000000), (0, 0), (0, 1), (1, 0)].all fun (a, b) =>
  [Ovf.addC, .subB].all fun o =>
    agrees (ovfProg o (v 0) (v 1)) (two a b) && agrees (ovfProg o (v 0) (i b)) (two a 0) &&
    agrees (ovfProg o (i a) (v 1)) (two 0 b) && agrees (ovfProg o (i a) (i b)) []

/-! ## Narrow arithmetic, `imul`, sign-extending loads, constant shifts -/

def sweepNarrow (_ : Unit) : Bool :=
  [BinOp.add, .sub, .and, .or, .xor, .mul].all fun o => [X86.Width.w8, .w16].all fun w =>
  edgeWords.all fun a => agrees (expr #[bin 9 o w (v 0) (v 1)]) (two a 0xffffffffffffff81)
#guard fired (expr #[bin 9 .add .w8 (v 0) (v 1)]) "alu.narrow"
#guard lastRow (expr #[bin 9 .mul .w64 (v 0) (i 127)]) == some (Select.row .imul .w64 .RMI8)
#guard lastRow (expr #[bin 9 .mul .w64 (v 0) (i 128)]) == some (Select.row .imul .w64 .RMI)
#guard lastRow (expr #[bin 9 .mul .w64 (v 0) (i 0x80000000)]) == some (Select.row .imul .w64 .RM)
def sweepImul (_ : Unit) : Bool :=
  [127, 128, 0x80000000, 0xffffffffffffffff].all fun k => [X86.Width.w8, .w16, .w32, .w64].all fun w =>
  agrees (expr #[bin 9 .mul w (v 0) (i k)]) (two 0xfedcba9876543210 0)

/-- Loads of each width and extension from a cell holding `v0`. -/
def loadProg (w : Width) (e : Ext) : Lir.Program :=
  expr #[heapBase, .store .w64 { base := some (.v 5) } (v 0), .assign 9 (.load w e { base := some (.v 5) })]
def sweepLoads (_ : Unit) : Bool :=
  [X86.Width.w8, .w16, .w32, .w64].all fun w => [Ext.zero, .sign].all fun e =>
  [0x8080808080808080, 0x7f7f7f7f7f7f7f7f, 0, 0xffffffffffffffff].all fun a => agrees (loadProg w e) (two a 0)
#guard fired (loadProg .w16 .sign) "load.sext"

def sweepShl (_ : Unit) : Bool :=
  [0, 1, 3, 4, 31, 32, 63, 64, 65].all fun s => [X86.Width.w8, .w16, .w32, .w64].all fun w =>
  agrees (expr #[bin 9 .shl w (v 0) (i s)]) (two 0x8000000180000003 0) &&
  agrees (expr #[bin 9 .shl w (i 0xf0f0f0f0f0f0f0f1) (i s)]) []
#guard fired (expr #[bin 9 .shl .w64 (v 0) (i 3)]) "shl.lea"
#guard fired (expr #[bin 9 .shl .w64 (v 0) (i 4)]) "shl.imul"
#guard fired (expr #[bin 9 .shl .w64 (v 0) (i 64)]) "shl.zero"

/-! ## Unsupported forms are named -/

#guard unsupportedForm (expr #[bin 9 .shr .w64 (v 0) (i 1)]) == some "shr.64"
#guard unsupportedForm (expr #[bin 9 .shl .w32 (v 0) (v 1)]) == some "shl.32 by a register"
#guard unsupportedForm (expr #[bin 9 .urem .w64 (v 0) (v 1)]) == some "urem.64"
#guard unsupportedForm (expr #[.assign 9 (.select .eq .w8 (v 0) (v 1) (v 0) (v 1))]) == some "select.8"
#guard unsupportedForm (expr #[.assign 9 (.test .ult .w16 (v 0) (v 1))]) == some "test.16"

/-! ## The clock -/

/-- A self-loop charges at every iteration at both levels. -/
def spin : Lir.Program := single (params := []) #[{ term := .jump (to 1) }, { term := .jump (to 1) }]

def lirCharges (p : Lir.Program) (k : Nat) : Nat :=
  match Lir.State.initial p [] (Region.initial 0) Region.ctx with
  | some s => (Props.countRun p 1000 k s).2.2
  | none => 0

def xvCharges (p : Lir.Program) (k : Nat) : Nat :=
  match select p with
  | .ok (q, _) =>
      match Xv.State.initial q [] (Region.initial 0) Region.ctx with
      | some s => (countRun q 1000 k s).2.2
      | none => 0
  | .error _ => 0

#guard lirCharges spin 7 == 7 && xvCharges spin 7 == 7
#guard agrees spin [] 7

/-! ## Well-formedness and operand metadata -/

def one (body : Array (Inst VReg)) (term : Term VReg := .ret [9]) : VProgram :=
  { funcs := #[{ params := [0, 1], results := 1, blocks := #[{ body, term }] }], main := 0 }

#guard (one #[.op (Select.row .add .w64 .MI8) [9] [.r 0, .i 5]]).wellFormed
/- No imm8 row at width 8, and 128 is not a canonical imm8. -/
#guard !(one #[.op (Select.row .add .w8 .MI8) [9] [.r 0, .i 5]]).wellFormed
#guard !(one #[.op (Select.row .add .w64 .MI8) [9] [.r 0, .i 128]]).wellFormed
/- A narrow write-only register destination keeps bits that are not an operand. -/
#guard !(one #[.op (Select.row .mov .w8 .OI) [9] [.i 5]]).wellFormed
#guard (one #[.op (Select.row .mov .w32 .OI) [9] [.i 5]]).wellFormed
/- Rows that do not bind, and a definition that is also a use. -/
#guard !(one #[.op (Select.row .add .w64 .MR) [9] [.r 0]]).wellFormed
#guard !(one #[.op (Select.row .add .w64 .MR) [0] [.r 0, .r 1]] (.ret [0])).wellFormed
/-- `imul` leaves ZF undefined, so it cannot feed `je`; it sets CF for `jc`. -/
def imulBranch (c : X86.Condition) : VProgram :=
  { funcs := #[{ params := [0, 1], results := 1, blocks := #[
      { term := .jcc (Select.row .imul .w64 .RM) [.r 0, .r 1] [2] c ⟨1, []⟩ ⟨2, []⟩ },
      { term := .ret [0] }, { term := .ret [1] }] }], main := 0 }
#guard !(imulBranch .eq).wellFormed
#guard (imulBranch .unsignedLt).wellFormed
#guard match Xv.eval (imulBranch .eq) 10 [3, 4] (Region.initial 0) Region.ctx with | .stuck => true | _ => false
#guard (Xv.eval (imulBranch .unsignedLt) 10 [3, 4] (Region.initial 0) Region.ctx).isOk

/- Operands: tied `add`s, a `lea` with base and index, 64- and 32-bit moves,
a store and a call. -/
#guard (Inst.operands (.op (Select.row .add .w64 .MI8) [9] [.r 0, .i 5] : Inst VReg)) ==
  [useAt .any 0, defAt (.reuse 0) 9]
#guard (Inst.operands (.op (Select.row .add .w32 .MR) [9] [.r 0, .r 1] : Inst VReg)) ==
  [useAt .reg 0, useAt .reg 1, defAt (.reuse 0) 9]
#guard (Inst.operands (.op Select.leaRow [9] [.m { base := some (.r 0), index := some (1, .four) }] : Inst VReg)) ==
  [useAt .reg 0, useAt .reg 1, defAt .reg 9]
#guard (Inst.operands (.op (Select.row .mov .w64 .MI) [9] [.i 5] : Inst VReg)) == [defAt .any 9]
#guard (Inst.operands (.op (Select.row .mov .w32 .RM) [9] [.r 0] : Inst VReg)) == [useAt .any 0, defAt .reg 9]
#guard (Inst.operands (.op (Select.row .mov .w64 .MR) [] [.m { base := some .ctx, disp := 8 }, .r 0] : Inst VReg)) ==
  [useAt .reg 0]
#guard (Inst.operands (.call 3 [0, 1] [9] : Inst VReg)) ==
  [useAt (.fixed .rdi) 0, useAt (.fixed .rsi) 1, defAt (.fixed .rax) 9]

/-- The edge-value sweeps: Lir against Xv at every width, operand shape and
boundary value above. `check-xv-select` runs them compiled. -/
def sweeps : List (String × (Unit → Bool)) :=
  [("rule 6: op r/m, imm8/imm32 at each width and boundary", sweepAluImm),
   ("rule 3: compare with a folded load, by load and compare width", sweepCmpLoad),
   ("rule 9: imul with a folded load, by load and multiply width", sweepMulLoad),
   ("rules 1–2: every condition, width and immediate side", sweepBranch),
   ("rule 4: carry and borrow boundaries, register and immediate operands", sweepOverflow),
   ("narrow arithmetic at w8/w16", sweepNarrow),
   ("imul by imm8/imm32/register at each width", sweepImul),
   ("loads at each width and extension", sweepLoads),
   ("shl by constants at each width", sweepShl)]

end CompilatrixTests.Xv.Cases
