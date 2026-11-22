import IxCC.X86.DriverSession

namespace IxCCTests.X86.DriverSession.Controls
open IxCC IxCC.X86 IxCC.X86.DriverSession
def driver : Driver := {
  base := 0, region := 65536, size := 4096, budget := 1024
  sp := 8192, ret := 12345, init := fun _ => 91, flags := {}, other := fun _ => 0 }
def session : Session := {
  linked := {
    object := ByteArray.empty, init := "cx_init", driver
    roots := [{ symbol := "cx_root", params := 1, ty := none }] } }
def isStuck {α : Type} : Sem.Result α → Bool
  | .stuck => true
  | _ => false
def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError label)
  IO.println ("PASS " ++ label)
def tests : IO Unit := do
  let bytes : Word → UInt8 := fun _ => 173
  check "missing root refuses" (isStuck (session.one ⟨1, [0]⟩ bytes 10))
  check "underapplication refuses" (isStuck (session.one ⟨0, []⟩ bytes 10))
  check "overapplication refuses" (isStuck (session.one ⟨0, [0,1]⟩ bytes 10))
  let overflow := match session.one ⟨0, [2^64]⟩ bytes 10 with
    | .resource .natOverflow => true
    | _ => false
  check "Nat overflow before empty object lookup" overflow
  check "actual empty object root refuses" (isStuck (session.one ⟨0, [0]⟩ bytes 10))
  check "actual empty object init refuses" (isStuck (session.run [] 10))
  check "actual empty object release refuses" (isStuck (session.dropCall 7 bytes 10))
  let empty := match session.runCalls [] bytes 0 with
    | .ok output => output.events.isEmpty && output.bytes 65536 == 173
    | _ => false
  check "empty continuation preserves bytes without init" empty
  check "high raw result word unchanged" (driver.regs [18446744073709551614] .rsi == 18446744073709551614)
  check "odd raw result word unchanged" (driver.regs [1] .rsi == 1)
  check "region byte unchanged by call setup" ((driver.mem bytes).bytes 65536 == 173)
  check "return slot receives caller return address" ((driver.mem bytes).read64 driver.sp == driver.ret)
  -- SIB canonicality: mov rax, [rsp] with scale=1 (SIB 0x24) succeeds;
  -- non-zero SIB scale bits (0x64, 0xa4, 0xe4) with index=none (index=4, rex.x=0) reject.
  check "canonical SIB no-index scale=1 decodes"
    ((Decode.decodeAt (ByteArray.mk #[0x48, 0x8b, 0x04, 0x24]) 0).isSome)
  check "non-canonical SIB no-index scale=2 rejected"
    ((Decode.decodeAt (ByteArray.mk #[0x48, 0x8b, 0x04, 0x64]) 0).isNone)
  check "non-canonical SIB no-index scale=4 rejected"
    ((Decode.decodeAt (ByteArray.mk #[0x48, 0x8b, 0x04, 0xa4]) 0).isNone)
  check "non-canonical SIB no-index scale=8 rejected"
    ((Decode.decodeAt (ByteArray.mk #[0x48, 0x8b, 0x04, 0xe4]) 0).isNone)
  -- Shift-by-zero flag preservation (`evalShift_zero_flags`)
  let sampleFlags : ByteEval.Flags := ⟨some true, some false, some true, some false⟩
  check "shiftFlags count=0 preserves prior flags"
    (ByteEval.shiftFlags .shl .w64 0x1234 0 sampleFlags == sampleFlags &&
     ByteEval.shiftFlags .shr .w32 0x1234 0 sampleFlags == sampleFlags &&
     ByteEval.shiftFlags .sar .w8 0x12 0 sampleFlags == sampleFlags)
  -- Driver.inText disjoint from mapped under canonical layout
  let canonDriver : Driver := {
    base := 0, region := 2 ^ 32, size := 2 ^ 26, budget := 2 ^ 23,
    sp := 2 ^ 40 + 8, ret := 2 ^ 46, init := fun _ => 0, flags := {}, other := fun _ => 0 }
  check "canonical driver text byte is inText and not mapped"
    (canonDriver.inText 4096 1024 && !canonDriver.mapped 1024)
  -- Wave 9 expanded x86-64 ISA subset reference vectors (243 total rows)
  check "Op.rows total count is 243" (Op.rows.length == 243)
  let baseCore : Core := (driver.core [0] bytes).setReg .rax 0x0123456789abcdef
    |>.setReg .rbx 0x0000000080000080
    |>.setReg .rcx 8
    |>.setReg .rdx 0xdeadbeefcafebabe
  -- 1. Unary ALU: `not` and `neg`
  let notOp : Op := { mn := .not, w := .w64, form := .M }
  let notOk := match notOp.exec [.reg .rax] baseCore sampleFlags with
    | .ok (c, f) => c.readReg .rax == 0xfedcba9876543210 && f == sampleFlags
    | .error _ => false
  check "not .w64 complements register and preserves flags"
    (notOk && Encode.encodeOp notOp [.reg .rax] == ByteArray.mk #[0x48, 0xf7, 0xd0])
  let negOp : Op := { mn := .neg, w := .w64, form := .M }
  let negOk := match negOp.exec [.reg .rax] (baseCore.setReg .rax 1) sampleFlags with
    | .ok (c, f) =>
        c.readReg .rax == 0xffffffffffffffff &&
        f.carry == some true && f.zero == some false && f.sign == some true && f.overflow == some false
    | .error _ => false
  check "neg .w64 two's-complements register and sets CF/ZF/SF/OF"
    (negOk && Encode.encodeOp negOp [.reg .rax] == ByteArray.mk #[0x48, 0xf7, 0xd8])
  -- 2. Widening unsigned multiply: `mul r/m` (`F7 /4`)
  let mulOp : Op := { mn := .mul, w := .w64, form := .M }
  let mulCore := baseCore.setReg .rax 0xffffffffffffffff |>.setReg .rbx 2
  let mulOk := match mulOp.exec [.reg .rbx] mulCore sampleFlags with
    | .ok (c, f) =>
        c.readReg .rax == 0xfffffffffffffffe &&
        c.readReg .rdx == 0x0000000000000001 &&
        f.carry == some true && f.overflow == some true &&
        f.zero == none && f.sign == none
    | .error _ => false
  check "mul .w64 computes 128-bit product in rdx:rax and sets CF=OF"
    (mulOk && Encode.encodeOp mulOp [.reg .rbx] == ByteArray.mk #[0x48, 0xf7, 0xe3])
  -- 3. Sub-word load & sign/zero extension: `mov .RM .w8/.w16`, `movzx .w64`, `movsx`, `movsxd`
  let mov8RM : Op := { mn := .mov, w := .w8, form := .RM }
  let mov8Ok := match mov8RM.exec [.reg .rax, .reg .rbx] baseCore sampleFlags with
    | .ok (c, _) => c.readReg .rax == 0x0123456789abcd80
    | .error _ => false
  check "mov .RM .w8 merges low byte into destination" mov8Ok
  let movzx64Op : Op := { mn := .movzx, w := .w64, form := .RM, src := .w8 }
  let movzx64Ok := match movzx64Op.exec [.reg .rax, .reg .rbx] baseCore sampleFlags with
    | .ok (c, _) => c.readReg .rax == 0x0000000000000080
    | .error _ => false
  check "movzx .w64 src=.w8 zero-extends byte to 64 bits" movzx64Ok
  let movsxOp : Op := { mn := .movsx, w := .w64, form := .RM, src := .w8 }
  let movsxOk := match movsxOp.exec [.reg .rax, .reg .rbx] baseCore sampleFlags with
    | .ok (c, _) => c.readReg .rax == 0xffffffffffffff80
    | .error _ => false
  check "movsx .w64 src=.w8 sign-extends byte to 64 bits"
    (movsxOk && Encode.encodeOp movsxOp [.reg .rax, .reg .rbx] == ByteArray.mk #[0x48, 0x0f, 0xbe, 0xc3])
  let movsxdOp : Op := { mn := .movsxd, w := .w64, form := .RM, src := .w32 }
  let movsxdOk := match movsxdOp.exec [.reg .rax, .reg .rbx] baseCore sampleFlags with
    | .ok (c, _) => c.readReg .rax == 0xffffffff80000080
    | .error _ => false
  check "movsxd .w64 src=.w32 sign-extends dword to 64 bits"
    (movsxdOk && Encode.encodeOp movsxdOp [.reg .rax, .reg .rbx] == ByteArray.mk #[0x48, 0x63, 0xc3])
  -- 4. Endianness & Bit Rotation: `bswap`, `rol`, `ror`
  let bswapOp : Op := { mn := .bswap, w := .w64, form := .O }
  let bswapOk := match bswapOp.exec [.reg .rax] (baseCore.setReg .rax 0x0102030405060708) sampleFlags with
    | .ok (c, f) => c.readReg .rax == 0x0807060504030201 && f == sampleFlags
    | .error _ => false
  check "bswap .w64 reverses all 8 bytes and preserves flags"
    (bswapOk && Encode.encodeOp bswapOp [.reg .rax] == ByteArray.mk #[0x48, 0x0f, 0xc8])
  let rolOp : Op := { mn := .rol, w := .w64, form := .MI }
  let rolOk := match rolOp.exec [.reg .rax, .imm 8] baseCore sampleFlags with
    | .ok (c, f) =>
        c.readReg .rax == 0x23456789abcdef01 &&
        f.carry == some true && f.zero == sampleFlags.zero && f.sign == sampleFlags.sign
    | .error _ => false
  check "rol .w64 rotates left by imm8 and preserves ZF/SF"
    (rolOk && Encode.encodeOp rolOp [.reg .rax, .imm 8] == ByteArray.mk #[0x48, 0xc1, 0xc0, 0x08])
  let rorOp : Op := { mn := .ror, w := .w64, form := .MC }
  let rorOk := match rorOp.exec [.reg .rax] baseCore sampleFlags with
    | .ok (c, f) =>
        c.readReg .rax == 0xef0123456789abcd &&
        f.carry == some true && f.zero == sampleFlags.zero && f.sign == sampleFlags.sign
    | .error _ => false
  check "ror .w64 rotates right by cl and preserves ZF/SF"
    (rorOk && Encode.encodeOp rorOp [.reg .rax] == ByteArray.mk #[0x48, 0xd3, 0xc8])
end IxCCTests.X86.DriverSession.Controls
