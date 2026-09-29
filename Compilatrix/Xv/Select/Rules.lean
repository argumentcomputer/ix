import Compilatrix.Xv.Select.Amode

/-!
# Statement rules

The rules for Lir statements (05 §4), each named for the firing counts:

| Lir | Xv | Rule |
| --- | --- | --- |
| `x := k` | `xor x32, x32`; `mov r32, imm32`; `mov r/m64, imm32`; `movabs` | 5 (`imm.*`) |
| `x := a` | `move` | `move` |
| `x := a op b` (add, sub, and, or, xor) | `op r/m, r`, tied to `a` | `alu.rr` |
| `x := a op k` | `op r/m, imm8` (83 /d) or `imm32` (81 /d), tied | 6 (`alu.imm8`, `alu.imm32`) |
| `x := a + b`, `a ± k` at w64, `a` live on | `lea x, [a + b·s + k]`, untied, with folding | 7 (`lea.add`) |
| `x := addr m` | `lea` | 8 (`lea.addr`) |
| `x := a * b`, `a * k` | `imul r, r/m` (tied), `imul r, r/m, imm8/imm32` | 12 (`imul.*`) |
| `x := a * (load m)` | `imul r, m` | 9 (`imul.load`) |
| `x := a << k` | `lea [a·2^k]` for `k ≤ 3` at w64, else `imul` by `2^k` | `shl.lea`, `shl.imul` |
| narrow (w8, w16) arithmetic | the w32 row, then `movzx` | `alu.narrow` |
| `x := load w zero m` | `mov r64/r32, m`, `movzx r32, m8/m16` | `load.*` |
| `x := load w sign m` | zero-extending load, `xor 2^(w−1)`, `add −2^(w−1)` | `load.sext` |
| `store w m a` | `mov m, r` or `mov m, imm` | `store.*` |
| `call` | `call`, immediates materialized | `call` |

Lir results are zero-extended at every width; 32-bit machine writes
zero-extend too, and narrower ones do not, so narrow arithmetic runs at
width 32 (its low bits depend only on its operands' low bits) and is
zero-extended with `movzx`. A sign-extending load uses `movzx`, `xor` and
`add` until `movsx` joins the table (05 §8.6 item 2).

**Waiting for M1.B1** (reported as unsupported forms): shifts right
(`shr`, `sar`) and left by a register (the `cl` rows), `udiv`/`urem`
(`div`), `select` (`cmovcc` in a fused pair) and `test` (`setcc` after
`xor`-zeroing, in a fused pair).
-/

namespace Compilatrix.Xv.Select

open Compilatrix.Lir (VReg Word)

def aluMnemonic : Lir.BinOp → X86.Mnemonic
  | .add => .add
  | .sub => .sub
  | .and => .and
  | .or => .or
  | _ => .xor

def narrowWidth (w : X86.Width) : Bool := w == .w8 || w == .w16

/-- The width a Lir operation at `w` runs at: 32 for narrow widths. -/
def opWidth (w : X86.Width) : X86.Width := if narrowWidth w then .w32 else w

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

/-- `x := a op b` for add, sub, and, or, xor. -/
def selectAlu (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) : SelM (List (Inst VReg)) := do
  if w == .w64 && (o == .add || o == .sub) then
    if let some out ← leaAdd? x o a b then return out
  let narrow := narrowWidth w
  let wo := opWidth w
  let dst ← if narrow then fresh else pure x
  let mn := aluMnemonic o
  let trunc (k : Word) : Word := if narrow then w.truncate k else k
  let body ← match a, b with
    | .v a, .v b => do
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
  if narrow then
    fire "alu.narrow"
    return body ++ [.op (row .movzx .w32 .RM w) [x] [.r dst]]
  return body

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
  if narrow then
    fire "alu.narrow"
    return body ++ [.op (row .movzx .w32 .RM w) [x] [.r dst]]
  return body

/-- `x := a << s` for a constant, already masked, count `s`. -/
def selectShlImm (i : Nat) (x : VReg) (w : X86.Width) (a : Lir.Arg) (s : Nat) : SelM (List (Inst VReg)) := do
  let (a, pre) ← argReg a
  if s == 0 then
    fire "shl.zero"
    return pre ++ truncTo w x a
  if w == .w64 && s ≤ 3 then
    match encodeTerms [(.r a, 2 ^ s)] 0 with
    | some am =>
        fire "shl.lea"
        return pre ++ [.op leaRow [x] [.m am]]
    | none => pure ()
  fire "shl.imul"
  return pre ++ (← selectMul i x w (.v a) (.imm (UInt64.ofNat (2 ^ s))))

/-- `x := a op b`. -/
def selectBin (i : Nat) (x : VReg) (o : Lir.BinOp) (w : X86.Width) (a b : Lir.Arg) :
    SelM (List (Inst VReg)) :=
  match o with
  | .add | .sub | .and | .or | .xor => selectAlu x o w a b
  | .mul => selectMul i x w a b
  | .shl =>
      match b with
      | .imm k => selectShlImm i x w a (k &&& Lir.shiftMask w).toNat
      | .v _ => unsupported s!"shl.{w.bits} by a register"
          "needs `shl r/m, cl` with the implicit `cl` operand (M1.B1)"
  | .shr => unsupported s!"shr.{w.bits}" "needs `shr r/m, imm8` and `shr r/m, cl` (M1.B1)"
  | .sar => unsupported s!"sar.{w.bits}" "needs `sar r/m, imm8` and `sar r/m, cl` (M1.B1)"
  | .udiv => unsupported s!"udiv.{w.bits}" "needs `div r/m` with implicit `rax`/`rdx` (M1.B1)"
  | .urem => unsupported s!"urem.{w.bits}" "needs `div r/m` with implicit `rax`/`rdx` (M1.B1)"

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
  | .select _ w .. => unsupported s!"select.{w.bits}"
      "needs `cmovcc` and a fused `cmp`/`cmovcc` pair (M1.B1)"
  | .test _ w .. => unsupported s!"test.{w.bits}"
      "needs `setcc` and a fused `xor`/`cmp`/`setcc` sequence (M1.B1)"

/-- The Xv instructions for statement `i`. -/
def selectStmt (i : Nat) : Lir.Stmt → SelM (List (Inst VReg))
  | .assign x r => selectAssign i x r
  | .store w m a => selectStore w m a
  | .call rs f as => do
      let (vs, pre) ← argRegs as
      fire "call"
      return pre ++ [.call f vs rs]

end Compilatrix.Xv.Select
