import Compilatrix.Xv.Select.Producer

/-!
# Statement rules

The rules for Lir statements (05 §4), each named for the firing counts:

| Lir | Xv | Rule |
| --- | --- | --- |
| `x := k` | `xor x32, x32`; `mov r32, imm32`; `mov r/m64, imm32`; `movabs` | 5 (`imm.*`) |
| `x := a` | `move` | `move` |
| `x := a op b` (add, sub, and, or, xor) | `op r/m, r`, tied to `a` | `alu.rr` |
| `x := a op k` | `op r/m, imm8` (83 /d) or `imm32` (81 /d), tied | 6 (`alu.imm8`, `alu.imm32`) |
| `x := a op (load m)` | `op r, m` (RM), tied | 9 (`alu.load`) |
| `x := a + b`, `a ± k` at w64, `a` live on | `lea x, [a + b·s + k]`, untied, with folding | 7 (`lea.add`) |
| `x := addr m` | `lea` | 8 (`lea.addr`) |
| `x := a * b`, `a * k` | `imul r, r/m` (tied), `imul r, r/m, imm8/imm32` | 12 (`imul.*`) |
| `x := a * (load m)` | `imul r, m` | 9 (`imul.load`) |
| `x := a shift k`, `a shift c` | `shl/shr/sar r/m, imm8` (C1), `r/m, cl` (D3, `c` fixed `rcx`), tied; `lea [a·2^k]` for a live-on `a`, `k ≤ 3` | 12 (`shift.imm`, `shift.cl`, `shl.lea`) |
| `x := a udiv b`, `a urem b` | `xor hi32, hi32; div r/m` with `a`, `hi` fixed `rax`, `rdx` | 12 (`div.quot`, `div.rem`, `div.load`) |
| `x := select c w a b t f` | `fused cmp/test (cmovcc)` with `x` tied to `f` | 10 (`select.cmov`) |
| `x := test c w a b` | `fused cmp/test (setcc)` with `x` zeroed first (an early definition) | 11 (`test.setcc`) |
| narrow (w8, w16) arithmetic | the w32 row (shifts: the w8/w16 row), then `movzx` | `alu.narrow` |
| `x := load w zero m` | `mov r64/r32, m`, `movzx r32, m8/m16` | `load.*` |
| `x := load w sign m` | zero-extending load, `xor 2^(w−1)`, `add −2^(w−1)` | `load.sext` |
| `store w m a` | `mov m, r` or `mov m, imm` | `store.*` |
| `call` | `call`, immediates materialized | `call` |

Lir results are zero-extended at every width; 32-bit machine writes
zero-extend too, and narrower ones do not, so narrow arithmetic runs at
width 32 (its low bits depend only on its operands' low bits), narrow
shifts run at their own width (a right shift reads only the low `w` bits),
and both are zero-extended with `movzx`; narrow division zero-extends its
operands to 32 bits first. Shift counts are masked alike by Lir and the
machine (63 at width 64, else 31). A sign-extending load uses `movzx`, `xor`
and `add` until `movsx` joins the table (05 §8.6 item 2).
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Word)

def aluMnemonic : Lir.BinOp → X86.Mnemonic
  | .add => .add
  | .sub => .sub
  | .and => .and
  | .or => .or
  | _ => .xor

def shiftMnemonic : Lir.BinOp → X86.Mnemonic
  | .shl => .shl
  | .shr => .shr
  | _ => .sar

def narrowWidth (w : X86.Width) : Bool := w == .w8 || w == .w16

/-- The width a Lir operation at `w` runs at: 32 for narrow widths. -/
def opWidth (w : X86.Width) : X86.Width := if narrowWidth w then .w32 else w

/-- Zero-extend a narrow result computed in `dst` into `x`. -/
def narrowed (w : X86.Width) (x dst : VReg) (body : List (Inst VReg)) : SelM (List (Inst VReg)) := do
  if narrowWidth w then
    fire "alu.narrow"
    return body ++ [.op (row .movzx .w32 .RM w) [x] [.r dst]]
  return body

/-- `dst := a op k` at width `wo`, tied to `a` (rule 6). -/
def aluImm (mn : X86.Mnemonic) (wo : X86.Width) (dst a : VReg) (k : Word) : SelM (List (Inst VReg)) := do
  match imm8? wo k with
  | some c =>
      fire "alu.imm8"
      return [.op (row mn wo .MI8) [dst] [.r a, .i c]]
  | none =>
  match immFull? wo k with
  | some c =>
      fire "alu.imm32"
      return [.op (row mn wo .MI) [dst] [.r a, .i c]]
  | none =>
      let (t, pre) ← materialize k
      fire "alu.rr"
      return pre ++ [.op (row mn wo .MR) [dst] [.r a, .r t]]

/-- The operand order for a tied commutative row: tie the operand that dies
here when the other lives on, so the allocator needs no copy. -/
def tieOrder (a b : VReg) : SelM (VReg × VReg) := do
  if (← useCount a) > 1 && (← useCount b) == 1 then
    fire "tie.swap"
    return (b, a)
  return (a, b)

/-- Rule 7: `x := a + b` or `a ± k` at width 64 as an untied `lea`, when an
operand lives on (so a tie would cost a copy) or address arithmetic folds
into it. -/
def leaAdd? (x : VReg) (o : Lir.BinOp) (a b : Lir.Arg) : SelM (Option (List (Inst VReg))) := do
  let (lin, regs) : Lin × List VReg := match o, a, b with
    | .add, .v a, .v b => ((Lin.ofArg (.v a)).add (Lin.ofArg (.v b)), [a, b])
    | .add, .v a, .imm k | .add, .imm k, .v a => ((Lin.ofArg (.v a)).add (Lin.ofArg (.imm k)), [a])
    | .sub, .v a, .imm k => ((Lin.ofArg (.v a)).add { disp := -(k.toNat : Int) }, [a])
    | _, _, _ => ({}, [])
  if regs.isEmpty then return none
  let (folded, used) ← foldLin lin
  let liveOn ← regs.allM fun r => return (← useCount r) > 1
  unless !used.isEmpty || liveOn do return none
  match folded.encode with
  | some am =>
      commitFold used
      fire "lea.add"
      return some [.op leaRow [x] [.m am]]
  | none => return none

/-- `x := a op b` for add, sub, and, or, xor, at statement `i`. -/
def selectAlu (i : Nat) (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) :
    SelM (List (Inst VReg)) := do
  if w == .w64 && (o == .add || o == .sub) then
    if let some out ← leaAdd? x o a b then return out
  let narrow := narrowWidth w
  let wo := opWidth w
  let dst ← if narrow then fresh else pure x
  let mn := aluMnemonic o
  let trunc (k : Word) : Word := if narrow then w.truncate k else k
  let body ← match a, b with
    | .v a, .v b => do
        -- Rule 9: a single-use load operand folds into `op r, m`.
        if let some m ← sinkLoad? b i wo.bytes then
          fire "alu.load"
          return ← narrowed w x dst [.op (row mn wo .RM) [dst] [.r a, .m m]]
        if o != .sub then
          if let some m ← sinkLoad? a i wo.bytes then
            fire "alu.load"
            return ← narrowed w x dst [.op (row mn wo .RM) [dst] [.r b, .m m]]
        let (a, b) ← if o == .sub then pure (a, b) else tieOrder a b
        fire "alu.rr"
        pure [.op (row mn wo .MR) [dst] [.r a, .r b]]
    | .v a, .imm k => aluImm mn wo dst a (trunc k)
    | .imm k, .v b =>
        if o == .sub then do
          let (t, pre) ← materialize k
          fire "alu.rr"
          pure (pre ++ [.op (row mn wo .MR) [dst] [.r t, .r b]])
        else do
          fire "alu.swap"
          aluImm mn wo dst b (trunc k)
    | .imm ka, .imm kb => do
        let (t, pre) ← materialize ka
        pure (pre ++ (← aluImm mn wo dst t (trunc kb)))
  narrowed w x dst body

/-- `dst := a * k` at width `wo` (untied three-operand `imul`). -/
def mulImm (wo : X86.Width) (dst a : VReg) (k : Word) : SelM (List (Inst VReg)) := do
  match imm8? wo k with
  | some c =>
      fire "imul.imm8"
      return [.op (row .imul wo .RMI8) [dst] [.r a, .i c]]
  | none =>
  match immFull? wo k with
  | some c =>
      fire "imul.imm32"
      return [.op (row .imul wo .RMI) [dst] [.r a, .i c]]
  | none =>
      let (t, pre) ← materialize k
      fire "imul.rr"
      return pre ++ [.op (row .imul wo .RM) [dst] [.r a, .r t]]

/-- `x := a * b` (rule 12's `imul`, and rule 9 for a folded load). -/
def selectMul (i : Nat) (x : VReg) (w : X86.Width) (a b : Lir.Arg) : SelM (List (Inst VReg)) := do
  let narrow := narrowWidth w
  let wo := opWidth w
  let dst ← if narrow then fresh else pure x
  let trunc (k : Word) : Word := if narrow then w.truncate k else k
  let rm := row .imul wo .RM
  let body ← match a, b with
    | .v a, .v b => do
        match ← sinkLoad? b i wo.bytes with
        | some m =>
            fire "imul.load"
            pure [.op rm [dst] [.r a, .m m]]
        | none =>
        match ← sinkLoad? a i wo.bytes with
        | some m =>
            fire "imul.load"
            pure [.op rm [dst] [.r b, .m m]]
        | none =>
            let (a, b) ← tieOrder a b
            fire "imul.rr"
            pure [.op rm [dst] [.r a, .r b]]
    | .v a, .imm k | .imm k, .v a => mulImm wo dst a (trunc k)
    | .imm ka, .imm kb => do
        let (t, pre) ← materialize ka
        pure (pre ++ (← mulImm wo dst t (trunc kb)))
  narrowed w x dst body

/-- `x := a shift b` (rule 12): by a constant count (already masked as Lir
and the machine mask it) or by a register in `cl`. -/
def selectShift (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) : SelM (List (Inst VReg)) := do
  let liveOn ← match a with
    | .v y => do pure (decide ((← useCount y) > 1))
    | .imm _ => pure false
  let (a, pre) ← argReg a
  let mn := shiftMnemonic o
  match b with
  | .imm k =>
      let s := (k &&& Lir.shiftMask w).toNat
      if s == 0 then
        fire "shift.zero"
        return pre ++ truncTo w x a
      if o == .shl && w == .w64 && s ≤ 3 && liveOn then
        if let some am := encodeTerms [(.r a, 2 ^ s)] 0 then
          fire "shl.lea"
          return pre ++ [.op leaRow [x] [.m am]]
      let dst ← if narrowWidth w then fresh else pure x
      fire "shift.imm"
      return pre ++ (← narrowed w x dst [.op (row mn w .MI) [dst] [.r a, .i (UInt64.ofNat s)]])
  | .v c =>
      let dst ← if narrowWidth w then fresh else pure x
      fire "shift.cl"
      return pre ++ (← narrowed w x dst [.op (row mn w .MC) [dst] [.r a, .r c]])

/-- `x := a udiv b` (`rem`: `urem`) at statement `i` (rule 12): `div` on
`rdx:rax` with the high half zeroed, so it never overflows; a zero divisor
is Lir's `stuck` and the row's `#DE` alike. Narrow widths divide the
zero-extended operands at width 32. A single-use load divisor folds. -/
def selectDiv (i : Nat) (x : VReg) (rem : Bool) (w : X86.Width) (a b : Lir.Arg) : SelM (List (Inst VReg)) := do
  let narrow := narrowWidth w
  let wo := opWidth w
  let (lo, preA) ← if narrow then argTrunc w a else argReg a
  let (divisor, preB) ← match b with
    | .v y =>
        if narrow then do
          let (t, pre) ← argTrunc w (.v y)
          pure (XArg.r t, pre)
        else do
          match ← sinkLoad? y i wo.bytes with
          | some m =>
              fire "div.load"
              pure (XArg.m m, [])
          | none => pure (XArg.r y, [])
    | .imm k => do
        let (t, pre) ← materialize (w.truncate k)
        pure (XArg.r t, pre)
  let hi ← fresh
  let q ← if rem then fresh else pure x
  let r ← if rem then pure x else fresh
  fire (if rem then "div.rem" else "div.quot")
  return preA ++ preB ++ [.zero hi, .op (X86.Op.divM wo) [q, r] [divisor, .r lo, .r hi]]

/-- `x := a op b`. -/
def selectBin (i : Nat) (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) :
    SelM (List (Inst VReg)) :=
  match o with
  | .add | .sub | .and | .or | .xor => selectAlu i x o w a b
  | .mul => selectMul i x w a b
  | .shl | .shr | .sar => selectShift x o w a b
  | .udiv => selectDiv i x false w a b
  | .urem => selectDiv i x true w a b

/-- Rule 10: `x := if c w a b then t else f` as a fused compare and `cmovcc`
(64-bit: `t` and `f` are whole words), `x` tied to `f`; a single-use
64-bit load `t` folds into the `cmovcc` source. -/
def selectSelect (i : Nat) (x : VReg) (c : Lir.Cond) (w : X86.Width) (a b t f : Lir.Arg) :
    SelM (List (Inst VReg)) := do
  let pr ← compareProducer c w a b
  let (f, preF) ← argReg f
  let (t, preT) ← match t with
    | .v y => do
        match ← sinkLoad? y i 8 with
        | some m =>
            fire "select.load"
            pure (XArg.m m, [])
        | none => pure (XArg.r y, [])
    | .imm k => do
        let (y, pre) ← materialize k
        pure (XArg.r y, pre)
  fire "select.cmov"
  return pr.pre ++ preF ++ preT ++ [.fused pr.op pr.args (X86.Op.cmovRM pr.cond .w64) [x] [.r f, t]]

/-- Rule 11: `x := if c w a b then 1 else 0` as a fused compare and
`setcc`, whose expansion zeroes `x` first. -/
def selectTest (x : VReg) (c : Lir.Cond) (w : X86.Width) (a b : Lir.Arg) : SelM (List (Inst VReg)) := do
  let pr ← compareProducer c w a b
  fire "test.setcc"
  return pr.pre ++ [.fused pr.op pr.args (X86.Op.setccM pr.cond) [x] []]

/-- A load, zero- or sign-extended. -/
def selectLoad (x : VReg) (w : X86.Width) (e : Lir.Ext) (m : Lir.Addr) : SelM (List (Inst VReg)) := do
  let am ← buildAmode m
  let zeroRow := match w with
    | .w64 => row .mov .w64 .RM
    | .w32 => row .mov .w32 .RM
    | w => row .movzx .w32 .RM w
  match w, e with
  | .w64, _ =>
      fire "load.mov64"
      return [.op zeroRow [x] [.m am]]
  | .w32, .zero =>
      fire "load.mov32"
      return [.op zeroRow [x] [.m am]]
  | _, .zero =>
      fire "load.movzx"
      return [.op zeroRow [x] [.m am]]
  | _, .sign =>
      -- sext z = (z ^ 2^(w−1)) − 2^(w−1), for z the zero-extended low w bits.
      let t ← fresh
      let t' ← fresh
      let bit : Word := UInt64.ofNat (2 ^ (w.bits - 1))
      let add ← aluImm .add .w64 x t' (0 - bit)
      fire "load.sext"
      return [.op zeroRow [t] [.m am], .op (row .xor .w32 .MI) [t'] [.r t, .i (X86.ImmKind.imm32.norm bit)]] ++ add

/-- A store; the address folds unless the fold would reach a protected
context cell. -/
def selectStore (w : X86.Width) (m : Lir.Addr) (a : Lir.Arg) : SelM (List (Inst VReg)) := do
  let (l, used) ← foldLin (Lin.ofAddr m)
  let am ← match l.encode with
    | some am =>
        if am.hitsProtectedCtx w.bytes then pure none
        else do
          commitFold used
          pure (some am)
    | none => pure none
  let am ← match am with
    | some am => pure am
    | none => match (Lin.ofAddr m).encode with
      | some am => pure am
      | none => unsupported "address" s!"displacement {m.disp} does not fit a signed 32-bit field"
  match a with
  | .v y =>
      fire "store.reg"
      return [.op (row .mov w .MR) [] [.m am, .r y]]
  | .imm k =>
      match immFull? w k with
      | some c =>
          fire "store.imm"
          return [.op (row .mov w .MI) [] [.m am, .i c]]
      | none =>
          let (t, pre) ← materialize k
          fire "store.reg"
          return pre ++ [.op (row .mov w .MR) [] [.m am, .r t]]

def selectAssign (i : Nat) (x : VReg) : Lir.Rhs → SelM (List (Inst VReg))
  | .arg (.v a) => do
      fire "move"
      return [.move x a]
  | .arg (.imm k) => movImm x k
  | .bin o w a b => selectBin i x o w a b
  | .load w e m => selectLoad x w e m
  | .addr m => do
      let am ← buildAmode m
      fire "lea.addr"
      return [.op leaRow [x] [.m am]]
  | .select c w a b t f => selectSelect i x c w a b t f
  | .test c w a b => selectTest x c w a b

/-- The Xv instructions for statement `i`. -/
def selectStmt (i : Nat) : Lir.Stmt → SelM (List (Inst VReg))
  | .assign x r => selectAssign i x r
  | .store w m a => selectStore w m a
  | .call rs f as => do
      let (vs, pre) ← argRegs as
      fire "call"
      return pre ++ [.call f vs rs]

end Compilatrix.Xv.Select
