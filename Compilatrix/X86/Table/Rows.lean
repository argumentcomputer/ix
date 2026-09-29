import Compilatrix.X86.Table.Op

/-!
# The x86 instruction table

`desc` describes every row and `Op.rows` lists the rows the compiler may
emit and the decoder may accept. `desc` is total, but only the listed rows
are meaningful: validation (`Instr.wellFormed`) and the decoder index both
range over `Op.rows`.

Families share their semantic function across widths and encodings, so an
ALU row's typed, byte and encoded meanings come from one place.
-/

namespace Compilatrix.X86

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

def mulSem (width : Width) : SemIn → Except SemFault SemOut
  | ⟨[left, right], _⟩ =>
      .ok { results := [left * right], flags := ByteEval.mulFlags width left right }
  | _ => .ok { results := [] }

def jccSem (condition : Condition) : SemIn → Except SemFault SemOut
  | ⟨_, flags⟩ =>
      match flags.test condition with
      | some taken => .ok { results := [], taken := some taken }
      | none => .error (.undefinedCondition condition)

def controlSem : SemIn → Except SemFault SemOut := fun _ => .ok { results := [] }

def allSet : Flag → FlagEffect := fun _ => .set

def mulEffect : Flag → FlagEffect
  | .cf | .of => .set
  | .zf | .sf => .undefined

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


/-- `op r/m, r` (00–39), `op r/m, imm` (80/81 /d) and `op r/m, imm8` (83 /d). -/
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
  | .mov => movDesc o.w o.form
  | .movzx => movzxDesc o.w o.src
  | .lea => leaDesc o.w
  | .imul => imulDesc o.w o.form
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
  widths.map (fun w => { mn := .mov, w, form := .MR }) ++
  [{ mn := .mov, w := .w32, form := .RM }, { mn := .mov, w := .w64, form := .RM }] ++
  widths.map (fun w => { mn := .mov, w, form := .OI }) ++
  [{ mn := .movzx, w := .w32, form := .RM, src := .w8 },
    { mn := .movzx, w := .w32, form := .RM, src := .w16 },
    { mn := .lea, w := .w64, form := .RM }] ++
  ([.w16, .w32, .w64] : List Width).map (fun w => { mn := .imul, w, form := .RM }) ++
  [{ mn := .push, w := .w64, form := .O }, { mn := .pop, w := .w64, form := .O },
    { mn := .call, w := .w64, form := .D32 }, { mn := .jmp, w := .w64, form := .D32 }] ++
  Condition.all.map (fun condition => { mn := .jcc condition, w := .w64, form := .D32 }) ++
  [{ mn := .ret, w := .w64, form := .ZO }]

/-- Control rows. -/
def Op.callRel32 : Op := { mn := .call, w := .w64, form := .D32 }
def Op.jmpRel32 : Op := { mn := .jmp, w := .w64, form := .D32 }
def Op.jccRel32 (condition : Condition) : Op := { mn := .jcc condition, w := .w64, form := .D32 }
def Op.retZO : Op := { mn := .ret, w := .w64, form := .ZO }

def slotsAccept : List Slot → List Arg → Bool
  | [], [] => true
  | slot :: slots, arg :: args => slot.kinds.any (·.accepts arg) && slotsAccept slots args
  | _, _ => false

/-- The operands have the row's slot kinds, with canonical immediates and
addresses. -/
def Op.argsOk (o : Op) (args : List Arg) : Bool := slotsAccept (desc o).slots args

end Compilatrix.X86
