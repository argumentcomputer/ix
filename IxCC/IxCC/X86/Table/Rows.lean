import IxCC.X86.Table.Op

/-!
# The x86 instruction table

`desc` describes every row and `Op.rows` lists the rows the compiler may
emit and the decoder may accept. `desc` is total, but only the listed rows
are meaningful: validation (`Instr.wellFormed`) and the decoder index both
range over `Op.rows`.

Families share their semantic function across widths and encodings, so an
ALU row's typed, byte and encoded meanings come from one place.
-/

namespace IxCC.X86

namespace Table

def rmSlot (width : Width) (role : Role) : Slot := ⟨[.reg, .mem], width, role⟩
def regSlot (width : Width) (role : Role) : Slot := ⟨[.reg], width, role⟩
def immSlot (kind : ArgKind) (width : Width) : Slot := ⟨[kind], width, .read⟩

def ImmKind.argKind : ImmKind → ArgKind
  | .imm8 => .imm8
  | .imm16 => .imm16
  | .imm32 => .imm32
  | .none | .imm64 => .imm64

/-- The full-size immediate of an `MI`/`RMI` row: 8 or 16 bits at those
widths, otherwise a sign-extended imm32. -/
def fullImm : Width → ImmKind
  | .w8 => .imm8
  | .w16 => .imm16
  | .w32 | .w64 => .imm32

/-- The immediate of a `mov r, imm` row: its full width, imm64 included. -/
def moveImm : Width → ImmKind
  | .w8 => .imm8
  | .w16 => .imm16
  | .w32 => .imm32
  | .w64 => .imm64

/-- Operand-size prefix and REX.W from the width. -/
def sized (width : Width) (enc : EncDesc) : EncDesc :=
  { enc with p66 := width == .w16, rexW := width == .w64 }

/-! ## Semantic functions -/

def aluSem (operation : AluOp) (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[left, right], _⟩ =>
      .ok { results := [operation.eval left right], flags := ByteEval.aluFlags operation width left right }
  | _ => .ok { results := [] }

def cmpSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[left, right], _⟩ => .ok { results := [], flags := ByteEval.aluFlags .sub width left right }
  | _ => .ok { results := [] }

def moveSem : SemIn → Except SemFault SemOut
  | ⟨[value], _⟩ => .ok { results := [value] }
  | _ => .ok { results := [] }

def zeroExtendSem (source : Width) : SemIn → Except SemFault SemOut
  | ⟨[value], _⟩ => .ok { results := [source.truncate value] }
  | _ => .ok { results := [] }

def signExtendSem (source : Width) : SemIn → Except SemFault SemOut
  | ⟨[value], _⟩ => .ok { results := [source.signExtend value] }
  | _ => .ok { results := [] }

def notSem : SemIn → Except SemFault SemOut
  | ⟨[value], _⟩ => .ok { results := [~~~value] }
  | _ => .ok { results := [] }

def negSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[value], _⟩ =>
      .ok { results := [0 - value]
            flags := ByteEval.aluFlags .sub width 0 value }
  | _ => .ok { results := [] }

def bswapSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[value], _⟩ => .ok { results := [width.bswap value] }
  | _ => .ok { results := [] }

def mulSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[left, right], _⟩ =>
      .ok { results := [left * right], flags := ByteEval.mulFlags width left right }
  | _ => .ok { results := [] }

/-- Widening unsigned `mul`: `rdx:rax := factor * rax` at `width`. Sets `CF`
and `OF` to whether the high half `rdx` is nonzero; `ZF` and `SF` are
undefined. -/
def umulSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[factor, low], _⟩ =>
      let product := (width.truncate factor).toNat * (width.truncate low).toNat
      let lowOut := UInt64.ofNat (product % 2 ^ width.bits)
      let highOut := UInt64.ofNat (product / 2 ^ width.bits)
      .ok { results := []
            implicit := [lowOut, highOut]
            flags := ByteEval.umulFlags (product / 2 ^ width.bits) }
  | _ => .ok { results := [] }

def jccSem (condition : Condition) : SemIn → Except SemFault SemOut
  | ⟨_, flags⟩ =>
      match flags.test condition with
      | some taken => .ok { results := [], taken := some taken }
      | none => .error (.undefinedCondition condition)

def controlSem : SemIn → Except SemFault SemOut := fun _ => .ok { results := [] }

/-- `test`: the flags of `and`, no result. -/
def testSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[left, right], _⟩ => .ok { results := [], flags := ByteEval.aluFlags .and width left right }
  | _ => .ok { results := [] }

/-- A shift of the destination by an imm8 or `cl` count. -/
def shiftSem (operation : ShiftOp) (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[value, count], _⟩ =>
      let count := shiftCount width count
      .ok { results := [⟨(operation.apply width value count).setWidth 64⟩]
            flags := ByteEval.shiftFlags operation width value count }
  | _ => .ok { results := [] }

/-- A rotation of the destination by an imm8 or `cl` count. -/
def rotateSem (operation : RotateOp) (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[value, count], _⟩ =>
      let count := shiftCount width count
      .ok { results := [⟨(operation.apply width value count).setWidth 64⟩]
            flags := ByteEval.rotateFlags operation width value count }
  | _ => .ok { results := [] }

/-- Unsigned `div`: the dividend is `rdx:rax` at the width, the divisor the
slot. `#DE` when the divisor is zero or the quotient does not fit, which is
exactly when the high half is not below the divisor. -/
def divSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[divisor, low, high], _⟩ =>
      let divisor := (width.truncate divisor).toNat
      let high := (width.truncate high).toNat
      if divisor == 0 || divisor ≤ high then .error .divideError
      else
        let dividend := high * 2 ^ width.bits + (width.truncate low).toNat
        .ok { results := [], implicit := [UInt64.ofNat (dividend / divisor), UInt64.ofNat (dividend % divisor)] }
  | _ => .ok { results := [] }

/-- `div` cannot fault: a nonzero divisor above the high half. -/
def divSafe (width : Width) (input : SemIn) : Bool :=
  match input.args with
  | [divisor, _, high] =>
      (width.truncate divisor).toNat != 0 && (width.truncate high).toNat < (width.truncate divisor).toNat
  | _ => true

/-- `setcc`: one if the condition holds on the flags, else zero. -/
def setccSem (condition : Condition) : SemIn → Except SemFault SemOut
  | ⟨_, flags⟩ =>
      match flags.test condition with
      | some holds => .ok { results := [if holds then 1 else 0] }
      | none => .error (.undefinedCondition condition)

/-- `cmovcc`: the source if the condition holds, else the destination. The
destination is written either way, so a 32-bit destination is zero-extended
even when the condition fails, and a memory source is always read. -/
def cmovSem (condition : Condition) : SemIn → Except SemFault SemOut
  | ⟨[destination, source], flags⟩ =>
      match flags.test condition with
      | some holds => .ok { results := [if holds then source else destination] }
      | none => .error (.undefinedCondition condition)
  | _ => .ok { results := [] }

def allSet : Flag → FlagEffect := fun _ => .set

def allUndefined : Flag → FlagEffect := fun _ => .undefined

def mulEffect : Flag → FlagEffect
  | .cf | .of => .set
  | .zf | .sf => .undefined

def rotateEffect : Flag → FlagEffect
  | .cf | .of => .set
  | .zf | .sf => .unchanged

/-! ## Row families -/

structure Arith where
  operation : Option AluOp
  digit : Nat
  wide : UInt8
  name : String

def addArith : Arith := ⟨some .add, 0, 0x01, "add"⟩
def orArith : Arith := ⟨some .or, 1, 0x09, "or"⟩
def andArith : Arith := ⟨some .and, 4, 0x21, "and"⟩
def subArith : Arith := ⟨some .sub, 5, 0x29, "sub"⟩
def xorArith : Arith := ⟨some .xor, 6, 0x31, "xor"⟩
def cmpArith : Arith := ⟨none, 7, 0x39, "cmp"⟩

def Arith.sem (arith : Arith) (width : Width) : SemIn → Except SemFault SemOut :=
  match arith.operation with
  | some operation => aluSem operation width
  | none => cmpSem width

def Arith.role (arith : Arith) : Role :=
  if arith.operation.isSome then .readWrite else .read


/-- `op r/m, r` (00–39), `op r, r/m` (02–3B), `op r/m, imm` (80/81 /d) and
`op r/m, imm8` (83 /d). -/
def arithDesc (arith : Arith) (width : Width) : OpEn → OpDesc
  | .MR =>
      { slots := [rmSlot width arith.role, regSlot width .read]
        sem := arith.sem width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then arith.wide - 1 else arith.wide
            modrm := .reg
            byteReg := width == .w8
            byteRM := width == .w8 }
        mnemonic := arith.name }
  | .RM =>
      { slots := [regSlot width arith.role, rmSlot width .read]
        sem := arith.sem width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then arith.wide + 1 else arith.wide + 2
            modrm := .reg
            byteReg := width == .w8
            byteRM := width == .w8 }
        mnemonic := arith.name }
  | .MI8 =>
      { slots := [rmSlot width arith.role, immSlot .imm8 width]
        sem := arith.sem width
        flagsOut := allSet
        enc := sized width { opcode := 0x83, modrm := .digit arith.digit, imm := .imm8 }
        mnemonic := arith.name }
  | _ =>
      { slots := [rmSlot width arith.role, immSlot (ImmKind.argKind (fullImm width)) width]
        sem := arith.sem width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then 0x80 else 0x81
            modrm := .digit arith.digit
            imm := fullImm width
            byteRM := width == .w8 }
        mnemonic := arith.name }

/-- `mov r/m, r` (88/89), `mov r, r/m` (8A/8B), `mov r, imm` (B0/B8+r) and
`mov r/m, imm` (C6/C7 /0). -/
def movDesc (width : Width) : OpEn → OpDesc
  | .RM =>
      { slots := [regSlot width .write, rmSlot width .read]
        sem := moveSem
        enc := sized width
          { opcode := if width == .w8 then 0x8a else 0x8b
            modrm := .reg
            byteReg := width == .w8
            byteRM := width == .w8 }
        mnemonic := "mov" }
  | .OI =>
      { slots := [regSlot width .write, immSlot (ImmKind.argKind (moveImm width)) width]
        sem := moveSem
        enc := sized width
          { opcode := if width == .w8 then 0xb0 else 0xb8
            emb := .regLow3
            imm := moveImm width
            byteReg := width == .w8 }
        mnemonic := if width == .w64 then "movabs" else "mov" }
  | .MI =>
      { slots := [rmSlot width .write, immSlot (ImmKind.argKind (fullImm width)) width]
        sem := moveSem
        enc := sized width
          { opcode := if width == .w8 then 0xc6 else 0xc7
            modrm := .digit 0
            imm := fullImm width
            byteRM := width == .w8 }
        mnemonic := "mov" }
  | _ =>
      { slots := [rmSlot width .write, regSlot width .read]
        sem := moveSem
        enc := sized width
          { opcode := if width == .w8 then 0x88 else 0x89
            modrm := .reg
            byteReg := width == .w8
            byteRM := width == .w8 }
        mnemonic := "mov" }

/-- `movzx r, r/m8` (0F B6) and `movzx r, r/m16` (0F B7). -/
def movzxDesc (width source : Width) : OpDesc :=
  { slots := [regSlot width .write, rmSlot source .read]
    sem := zeroExtendSem source
    enc := sized width
      { map := .x0F
        opcode := if source == .w8 then 0xb6 else 0xb7
        modrm := .reg
        byteRM := source == .w8 }
    mnemonic := "movzx" }

/-- `movsx r, r/m8` (0F BE) and `movsx r, r/m16` (0F BF). -/
def movsxDesc (width source : Width) : OpDesc :=
  { slots := [regSlot width .write, rmSlot source .read]
    sem := signExtendSem source
    enc := sized width
      { map := .x0F
        opcode := if source == .w8 then 0xbe else 0xbf
        modrm := .reg
        byteRM := source == .w8 }
    mnemonic := "movsx" }

/-- `movsxd r64, r/m32` (REX.W + 63 /r). -/
def movsxdDesc (width : Width) : OpDesc :=
  { slots := [regSlot width .write, rmSlot .w32 .read]
    sem := signExtendSem .w32
    enc := sized width { opcode := 0x63, modrm := .reg }
    mnemonic := "movsxd" }

/-- `not r/m` (F6/F7 /2). -/
def notDesc (width : Width) : OpDesc :=
  { slots := [rmSlot width .readWrite]
    sem := notSem
    enc := sized width
      { opcode := if width == .w8 then 0xf6 else 0xf7
        modrm := .digit 2
        byteRM := width == .w8 }
    mnemonic := "not" }

/-- `neg r/m` (F6/F7 /3). -/
def negDesc (width : Width) : OpDesc :=
  { slots := [rmSlot width .readWrite]
    sem := negSem width
    flagsOut := allSet
    enc := sized width
      { opcode := if width == .w8 then 0xf6 else 0xf7
        modrm := .digit 3
        byteRM := width == .w8 }
    mnemonic := "neg" }

/-- `bswap r32` (0F C8+rd) and `bswap r64` (REX.W + 0F C8+rd). -/
def bswapDesc (width : Width) : OpDesc :=
  { slots := [regSlot width .readWrite]
    sem := bswapSem width
    enc := sized width { map := .x0F, opcode := 0xc8, emb := .regLow3 }
    mnemonic := "bswap" }

/-- `lea r, m` (8D); the memory slot contributes its address. -/
def leaDesc (width : Width) : OpDesc :=
  { slots := [regSlot width .write, ⟨[.mem], width, .address⟩]
    sem := moveSem
    enc := sized width { opcode := 0x8d, modrm := .reg }
    mnemonic := "lea" }

/-- `imul r, r/m` (0F AF), `imul r, r/m, imm8` (6B) and `imul r, r/m, imm` (69). -/
def imulDesc (width : Width) : OpEn → OpDesc
  | .RMI8 =>
      { slots := [regSlot width .write, rmSlot width .read, immSlot .imm8 width]
        sem := mulSem width
        flagsOut := mulEffect
        enc := sized width { opcode := 0x6b, modrm := .reg, imm := .imm8 }
        mnemonic := "imul" }
  | .RMI =>
      { slots := [regSlot width .write, rmSlot width .read, immSlot (ImmKind.argKind (fullImm width)) width]
        sem := mulSem width
        flagsOut := mulEffect
        enc := sized width { opcode := 0x69, modrm := .reg, imm := fullImm width }
        mnemonic := "imul" }
  | _ =>
      { slots := [regSlot width .readWrite, rmSlot width .read]
        sem := mulSem width
        flagsOut := mulEffect
        enc := sized width { map := .x0F, opcode := 0xaf, modrm := .reg }
        mnemonic := "imul" }

/-- `test r/m, r` (84/85) and `test r/m, imm` (F6/F7 /0). -/
def testDesc (width : Width) : OpEn → OpDesc
  | .MR =>
      { slots := [rmSlot width .read, regSlot width .read]
        sem := testSem width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then 0x84 else 0x85
            modrm := .reg
            byteReg := width == .w8
            byteRM := width == .w8 }
        mnemonic := "test" }
  | _ =>
      { slots := [rmSlot width .read, immSlot (ImmKind.argKind (fullImm width)) width]
        sem := testSem width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then 0xf6 else 0xf7
            modrm := .digit 0
            imm := fullImm width
            byteRM := width == .w8 }
        mnemonic := "test" }

def _root_.IxCC.X86.ShiftOp.digit : ShiftOp → Nat
  | .shl => 4
  | .shr => 5
  | .sar => 7

def _root_.IxCC.X86.ShiftOp.name : ShiftOp → String
  | .shl => "shl"
  | .shr => "shr"
  | .sar => "sar"

/-- `shl`/`shr`/`sar r/m, imm8` (C0/C1 /4,/5,/7) and `r/m, cl` (D2/D3 /4,/5,/7,
with `cl` implicit). -/
def shiftDesc (operation : ShiftOp) (width : Width) : OpEn → OpDesc
  | .MC =>
      { slots := [rmSlot width .readWrite]
        implicit := [⟨.rcx, .w8, .read⟩]
        sem := shiftSem operation width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then 0xd2 else 0xd3
            modrm := .digit operation.digit
            byteRM := width == .w8 }
        mnemonic := operation.name }
  | _ =>
      { slots := [rmSlot width .readWrite, immSlot .imm8 width]
        sem := shiftSem operation width
        flagsOut := allSet
        enc := sized width
          { opcode := if width == .w8 then 0xc0 else 0xc1
            modrm := .digit operation.digit
            imm := .imm8
            byteRM := width == .w8 }
        mnemonic := operation.name }

def _root_.IxCC.X86.RotateOp.digit : RotateOp → Nat
  | .rol => 0
  | .ror => 1

def _root_.IxCC.X86.RotateOp.name : RotateOp → String
  | .rol => "rol"
  | .ror => "ror"

/-- `rol`/`ror r/m, imm8` (C0/C1 /0,/1) and `r/m, cl` (D2/D3 /0,/1, with `cl`
implicit). -/
def rotateDesc (operation : RotateOp) (width : Width) : OpEn → OpDesc
  | .MC =>
      { slots := [rmSlot width .readWrite]
        implicit := [⟨.rcx, .w8, .read⟩]
        sem := rotateSem operation width
        flagsOut := rotateEffect
        enc := sized width
          { opcode := if width == .w8 then 0xd2 else 0xd3
            modrm := .digit operation.digit
            byteRM := width == .w8 }
        mnemonic := operation.name }
  | _ =>
      { slots := [rmSlot width .readWrite, immSlot .imm8 width]
        sem := rotateSem operation width
        flagsOut := rotateEffect
        enc := sized width
          { opcode := if width == .w8 then 0xc0 else 0xc1
            modrm := .digit operation.digit
            imm := .imm8
            byteRM := width == .w8 }
        mnemonic := operation.name }

/-- Unsigned widening `mul r/m` (F7 /4): implicit `rax` (factor and low half)
and `rdx` (high half) at the width. -/
def umulDesc (width : Width) : OpDesc :=
  { slots := [rmSlot width .read]
    implicit := [⟨.rax, width, .readWrite⟩, ⟨.rdx, width, .write⟩]
    sem := umulSem width
    flagsOut := mulEffect
    enc := sized width { opcode := 0xf7, modrm := .digit 4 }
    mnemonic := "mul" }

/-- Unsigned `div r/m` (F7 /6): implicit `rax` and `rdx` at the width. -/
def divDesc (width : Width) : OpDesc :=
  { slots := [rmSlot width .read]
    implicit := [⟨.rax, width, .readWrite⟩, ⟨.rdx, width, .readWrite⟩]
    sem := divSem width
    flagsOut := allUndefined
    safe := divSafe width
    enc := sized width { opcode := 0xf7, modrm := .digit 6 }
    mnemonic := "div" }

def pushDesc : OpDesc :=
  { slots := [regSlot .w64 .read]
    stack := .push
    sem := moveSem
    enc := { opcode := 0x50, emb := .regLow3 }
    mnemonic := "push" }

def popDesc : OpDesc :=
  { slots := [regSlot .w64 .write]
    stack := .pop
    sem := moveSem
    enc := { opcode := 0x58, emb := .regLow3 }
    mnemonic := "pop" }

def relSlot : Slot := ⟨[.rel32], .w64, .read⟩

def callDesc : OpDesc :=
  { slots := [relSlot]
    stack := .push
    sem := controlSem
    enc := { opcode := 0xe8, imm := .imm32 }
    mnemonic := "call" }

def jmpDesc : OpDesc :=
  { slots := [relSlot]
    sem := controlSem
    enc := { opcode := 0xe9, imm := .imm32 }
    mnemonic := "jmp" }

def retDesc : OpDesc :=
  { slots := []
    stack := .pop
    sem := controlSem
    enc := { opcode := 0xc3 }
    mnemonic := "ret" }

end Table

/-- The low nibble of `Jcc` (0F 80+cc). -/
def Condition.code : Condition → UInt8
  | .eq => 0x4
  | .ne => 0x5
  | .unsignedLt => 0x2
  | .unsignedLe => 0x6
  | .unsignedGt => 0x7
  | .unsignedGe => 0x3
  | .signedLt => 0xc
  | .signedLe => 0xe
  | .signedGt => 0xf
  | .signedGe => 0xd

def Condition.suffix : Condition → String
  | .eq => "e"
  | .ne => "ne"
  | .unsignedLt => "b"
  | .unsignedLe => "be"
  | .unsignedGt => "a"
  | .unsignedGe => "ae"
  | .signedLt => "l"
  | .signedLe => "le"
  | .signedGt => "g"
  | .signedGe => "ge"

namespace Table

def jccDesc (condition : Condition) : OpDesc :=
  { slots := [relSlot]
    sem := jccSem condition
    flagsIn := condition.reads
    safe := fun input => (input.flags.test condition).isSome
    enc := { map := .x0F, opcode := 0x80 + condition.code, imm := .imm32 }
    mnemonic := "j" ++ condition.suffix }

/-- `setcc r/m8` (0F 90+cc /0). -/
def setccDesc (condition : Condition) : OpDesc :=
  { slots := [rmSlot .w8 .write]
    sem := setccSem condition
    flagsIn := condition.reads
    safe := fun input => (input.flags.test condition).isSome
    enc := { map := .x0F, opcode := 0x90 + condition.code, modrm := .digit 0, byteRM := true }
    mnemonic := "set" ++ condition.suffix }

/-- `cmovcc r, r/m` (0F 40+cc). -/
def cmovDesc (condition : Condition) (width : Width) : OpDesc :=
  { slots := [regSlot width .readWrite, rmSlot width .read]
    sem := cmovSem condition
    flagsIn := condition.reads
    safe := fun input => (input.flags.test condition).isSome
    enc := sized width { map := .x0F, opcode := 0x40 + condition.code, modrm := .reg }
    mnemonic := "cmov" ++ condition.suffix }

end Table


open Table in
/-- The table. Meaningful on `Op.rows`. -/
def desc (o : Op) : OpDesc :=
  match o.mn with
  | .add => arithDesc addArith o.w o.form
  | .or => arithDesc orArith o.w o.form
  | .and => arithDesc andArith o.w o.form
  | .sub => arithDesc subArith o.w o.form
  | .xor => arithDesc xorArith o.w o.form
  | .cmp => arithDesc cmpArith o.w o.form
  | .not => notDesc o.w
  | .neg => negDesc o.w
  | .mov => movDesc o.w o.form
  | .movzx => movzxDesc o.w o.src
  | .movsx => movsxDesc o.w o.src
  | .movsxd => movsxdDesc o.w
  | .lea => leaDesc o.w
  | .imul => imulDesc o.w o.form
  | .mul => umulDesc o.w
  | .test => testDesc o.w o.form
  | .shl => shiftDesc .shl o.w o.form
  | .shr => shiftDesc .shr o.w o.form
  | .sar => shiftDesc .sar o.w o.form
  | .rol => rotateDesc .rol o.w o.form
  | .ror => rotateDesc .ror o.w o.form
  | .bswap => bswapDesc o.w
  | .div => divDesc o.w
  | .setcc condition => setccDesc condition
  | .cmovcc condition => cmovDesc condition o.w
  | .push => pushDesc
  | .pop => popDesc
  | .call => callDesc
  | .jmp => jmpDesc
  | .jcc condition => jccDesc condition
  | .ret => retDesc

def Condition.all : List Condition :=
  [.eq, .ne, .unsignedLt, .unsignedLe, .unsignedGt, .unsignedGe,
    .signedLt, .signedLe, .signedGt, .signedGe]

/-- The rows the compiler may emit and the decoder accepts. -/
def Op.rows : List Op :=
  let widths : List Width := [.w8, .w16, .w32, .w64]
  let arith : List Mnemonic := [.add, .or, .and, .sub, .xor, .cmp]
  arith.flatMap (fun mn => widths.map fun w => { mn, w, form := .MR }) ++
  arith.flatMap (fun mn => widths.map fun w => { mn, w, form := .MI }) ++
  arith.flatMap (fun mn => ([.w16, .w32, .w64] : List Width).map fun w => { mn, w, form := .MI8 }) ++
  widths.map (fun w => { mn := .mov, w, form := .MR }) ++
  widths.map (fun w => { mn := .mov, w, form := .RM }) ++
  widths.map (fun w => { mn := .mov, w, form := .OI }) ++
  widths.map (fun w => { mn := .mov, w, form := .MI }) ++
  [{ mn := .movzx, w := .w32, form := .RM, src := .w8 },
    { mn := .movzx, w := .w32, form := .RM, src := .w16 },
    { mn := .movzx, w := .w64, form := .RM, src := .w8 },
    { mn := .movzx, w := .w64, form := .RM, src := .w16 },
    { mn := .movsx, w := .w16, form := .RM, src := .w8 },
    { mn := .movsx, w := .w32, form := .RM, src := .w8 },
    { mn := .movsx, w := .w64, form := .RM, src := .w8 },
    { mn := .movsx, w := .w32, form := .RM, src := .w16 },
    { mn := .movsx, w := .w64, form := .RM, src := .w16 },
    { mn := .movsxd, w := .w64, form := .RM, src := .w32 },
    { mn := .lea, w := .w64, form := .RM }] ++
  ([.w16, .w32, .w64] : List Width).flatMap (fun w =>
    [{ mn := .imul, w, form := .RM }, { mn := .imul, w, form := .RMI8 }, { mn := .imul, w, form := .RMI }]) ++
  [{ mn := .push, w := .w64, form := .O }, { mn := .pop, w := .w64, form := .O },
    { mn := .call, w := .w64, form := .D32 }, { mn := .jmp, w := .w64, form := .D32 }] ++
  Condition.all.map (fun condition => { mn := .jcc condition, w := .w64, form := .D32 }) ++
  [{ mn := .ret, w := .w64, form := .ZO }] ++
  arith.flatMap (fun mn => widths.map fun w => { mn, w, form := .RM }) ++
  widths.map (fun w => { mn := .not, w, form := .M }) ++
  widths.map (fun w => { mn := .neg, w, form := .M }) ++
  widths.map (fun w => { mn := .test, w, form := .MR }) ++
  widths.map (fun w => { mn := .test, w, form := .MI }) ++
  ([.shl, .shr, .sar, .rol, .ror] : List Mnemonic).flatMap (fun mn =>
    widths.flatMap fun w => [{ mn, w, form := .MI }, { mn, w, form := .MC }]) ++
  ([.w32, .w64] : List Width).map (fun w => { mn := .bswap, w, form := .O }) ++
  ([.w32, .w64] : List Width).map (fun w => { mn := .mul, w, form := .M }) ++
  ([.w32, .w64] : List Width).map (fun w => { mn := .div, w, form := .M }) ++
  Condition.all.map (fun condition => { mn := .setcc condition, w := .w8, form := .M }) ++
  Condition.all.flatMap (fun condition =>
    ([.w16, .w32, .w64] : List Width).map fun w => { mn := .cmovcc condition, w, form := .RM })

/-- Control rows. -/
def Op.callRel32 : Op := { mn := .call, w := .w64, form := .D32 }
def Op.jmpRel32 : Op := { mn := .jmp, w := .w64, form := .D32 }
def Op.jccRel32 (condition : Condition) : Op := { mn := .jcc condition, w := .w64, form := .D32 }
def Op.retZO : Op := { mn := .ret, w := .w64, form := .ZO }

/-- Rows the backend selects by name. -/
def Op.mulM (width : Width) : Op := { mn := .mul, w := width, form := .M }
def Op.divM (width : Width) : Op := { mn := .div, w := width, form := .M }
def Op.setccM (condition : Condition) : Op := { mn := .setcc condition, w := .w8, form := .M }
def Op.cmovRM (condition : Condition) (width : Width) : Op := { mn := .cmovcc condition, w := width, form := .RM }

/-- A producer defines every flag its consumer reads (note 05 §3): the
consumer of a fused pair, or the `jcc` of a branch, sees only flags the
producer has just computed, never older ones. -/
def FusedOk (producer consumer : Op) : Bool :=
  (desc consumer).flagsIn.all fun flag => (desc producer).flagsOut flag == .set

/-- A row that writes nothing but flags (`cmp`, `test`): no written slot,
implicit register or stack traffic. Only these produce a fused pair's
flags, so the consumer runs on the unchanged core. -/
def Op.flagsOnly (o : Op) : Bool :=
  (desc o).slots.all (fun slot => !slot.role.writes) &&
    (desc o).implicit.all (fun implicit => !implicit.role.writes) && (desc o).stack == .none

def slotsAccept : List Slot → List Arg → Bool
  | [], [] => true
  | slot :: slots, arg :: args => slot.kinds.any (·.accepts arg) && slotsAccept slots args
  | _, _ => false

/-- The operands have the row's slot kinds, with canonical immediates and
addresses. -/
def Op.argsOk (o : Op) (args : List Arg) : Bool := slotsAccept (desc o).slots args

end IxCC.X86
