import Compilatrix.Tools.Check
import Compilatrix.X86.ByteEval
import Compilatrix.X86.Encode

/-! Hardware-differential gate for the local x86 byte model.

Every case is real encoder output. The native harness
(`fixtures/x86/hw_diff_harness.c`) runs it on the host CPU from fixed
registers, flags and pattern-filled pages; `ByteEval` runs the same bytes from
the same state. The gate compares:
- the exit (fall-through or taken);
- all sixteen registers;
- every flag the model defines;
- every changed page byte;
- memory faults.

This tests, rather than proves, that the local model agrees with the
processor; the trust ledger records it as such. -/

open Compilatrix Compilatrix.X86 Compilatrix.Tools.Check

namespace CheckX86Hardware

def testAddress : Word := 0x40000800
def takenAddress : Word := 0x40000c00
def dataPage : Word := 0x40100000
def stackPage : Word := 0x40200000
def pageSize : Word := 4096
def stackTop : Word := stackPage + 0x800

/-- The harness's deterministic page contents. -/
def pattern (seed address : Word) : UInt8 :=
  let x := seed ^^^ (address * 0x9e3779b97f4a7c15)
  let x := x ^^^ (x >>> 29)
  let x := x * 0xbf58476d1ce4e5b9
  let x := x ^^^ (x >>> 32)
  x.toUInt8

def mapped (address : Word) : Bool :=
  (dataPage ≤ address && address < dataPage + pageSize) ||
    (stackPage ≤ address && address < stackPage + pageSize)

def registerOrder : Array GPR :=
  #[.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
    .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

structure Case where
  id : String
  code : ByteArray
  registers : Array Word
  /-- Input flags as the harness bits: 0 CF, 6 ZF, 7 SF, 11 OF. -/
  flags : Word
  seed : Word
  /-- Whether the case can write memory, so the model scans both pages. -/
  writes : Bool := false

def Case.line (c : Case) : String :=
  let hexWord (w : Word) := hexNat w.toNat
  let code := c.code.data.foldl (fun s b => s ++ (if b.toNat < 16 then "0" else "") ++ hexNat b.toNat) ""
  " ".intercalate ([c.id, code] ++ c.registers.toList.map hexWord ++ [hexWord c.flags, hexWord c.seed])

def bit (flags : Word) (index : Nat) : Bool := (flags >>> UInt64.ofNat index) &&& 1 == 1

def Case.initial (c : Case) : ByteEval.State :=
  { core := {
      registers := fun register =>
        match registerOrder.findIdx? (· == register) with
        | some i => c.registers[i]!
        | none => 0
      memory := {
        bytes := pattern c.seed
        readable := mapped
        writable := mapped } }
    rip := testAddress
    flags := {
      carry := some (bit c.flags 0), zero := some (bit c.flags 6),
      sign := some (bit c.flags 7), overflow := some (bit c.flags 11) } }

/-- Observations: `none` for a memory fault; otherwise exit, registers,
the four modeled flags, and changed bytes (address, value). -/
structure Observed where
  exit : Nat
  registers : Array Word
  flags : ByteEval.Flags
  changed : Array (Word × UInt8)

def pageBytes : Array Word :=
  (Array.range pageSize.toNat).map (dataPage + ·.toUInt64) ++
    (Array.range pageSize.toNat).map (stackPage + ·.toUInt64)

/-- Run the model over the case bytes until control leaves them. -/
def model (c : Case) : Except String (Option Observed) := do
  let finish := testAddress + c.code.size.toUInt64
  let rec loop : Nat → ByteEval.State → Except String (Option Observed)
    | 0, _ => throw "model did not leave the case bytes"
    | fuel + 1, state =>
      if state.rip == finish || state.rip == takenAddress then
        let changed := if c.writes then
            pageBytes.filterMap fun a =>
              let v := state.core.memory.bytes a
              if v != pattern c.seed a then some (a, v) else none
          else #[]
        pure (some {
          exit := if state.rip == takenAddress then 1 else 0
          registers := registerOrder.map state.core.readReg
          flags := state.flags
          changed })
      else if state.rip < testAddress || finish < state.rip then
        throw s!"model left the case window at {hexNat state.rip.toNat}"
      else
        match ByteEval.step c.code testAddress state with
        | .ok next => loop fuel next
        | .error (.memory _) => pure none
        | .error fault => throw s!"model fault {repr fault}"
  loop 8 c.initial

/-- Parse one harness output line. -/
def parseNative (line : String) : Except String (String × Option (Nat × Array Word × Word × Array (Word × UInt8))) := do
  let parts := line.splitOn " " |>.filter (· != "")
  match parts with
  | id :: "fault" :: _ => return (id, none)
  | id :: "ok" :: exit :: rest =>
    let hex (s : String) : Except String Word := do
      let bytes ← unhex (if s.length % 2 == 1 then "0" ++ s else s)
      return bytes.data.foldl (fun acc b => (acc <<< 8) ||| b.toUInt64) 0
    let registers ← (rest.take 16).mapM hex
    let flags ← hex (rest.getD 16 "0")
    let changed ← (rest.drop 18).mapM fun pair => do
      let [address, value] := pair.splitOn "=" | throw s!"bad byte {pair}"
      return (← hex address, (← hex value).toUInt8)
    return (id, some (exit.toNat!, registers.toArray, flags, changed.toArray))
  | _ => throw s!"unparsed harness line: {line}"

/-- Compare one case; the result is the list of differences. -/
def compare (c : Case) (native : Option (Nat × Array Word × Word × Array (Word × UInt8))) :
    Except String (List String) := do
  let expected ← model c
  match expected, native with
  | none, none => return []
  | none, some _ => return ["model faults, processor does not"]
  | some _, none => return ["processor faults, model does not"]
  | some m, some (exit, registers, flags, changed) =>
    let mut errors := []
    if m.exit != exit then errors := s!"exit model {m.exit} native {exit}" :: errors
    for i in [:16] do
      if m.registers[i]! != registers[i]! then
        errors := s!"{repr registerOrder[i]!}: model {hexNat m.registers[i]!.toNat} native {hexNat registers[i]!.toNat}" :: errors
    let check (label : String) (value : Option Bool) (index : Nat) : List String :=
      match value with
      | some v => if v != bit flags index then [s!"flag {label}: model {v}"] else []
      | none => []
    errors := errors ++ check "CF" m.flags.carry 0 ++ check "ZF" m.flags.zero 6 ++
      check "SF" m.flags.sign 7 ++ check "OF" m.flags.overflow 11
    if c.writes && m.changed != changed then
      errors := s!"memory: model {m.changed.size} changed bytes, native {changed.size}" :: errors
    if !c.writes && !changed.isEmpty then
      errors := s!"unexpected native memory writes: {changed.size}" :: errors
    return errors

/-! ## Case generation -/

def edges : Array Word :=
  #[0, 1, 2, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x7fffffff, 0x80000000,
    0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
    0xfffffffffffffffe, 0xffffffffffffffff]

/-- Deterministic xorshift stream. -/
def next (state : Word) : Word :=
  let x := state ^^^ (state <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def gprs : Array GPR := registerOrder

/-- Registers for case `n`: edge or random values, `rsp` inside the stack page. -/
def registersFor (n : Nat) : Array Word := Id.run do
  let mut state : Word := 0x243f6a8885a308d3 + n.toUInt64 * 0x13198a2e03707344
  let mut out := #[]
  for i in [:16] do
    state := next state
    let value := if state % 3 == 0 then edges[(state >>> 8).toNat % edges.size]! else next state
    out := out.push (if i == 4 then stackTop else value)
  return out

def widths : Array Width := #[.w8, .w16, .w32, .w64]
def aluOps : Array AluOp := #[.add, .sub, .and, .or, .xor]
def conditions : Array Condition := #[.eq, .ne, .unsignedLt, .unsignedLe, .unsignedGt,
  .unsignedGe, .signedLt, .signedLe, .signedGt, .signedGe]

def rel32 (opcode : List UInt8) (after : Word) : ByteArray :=
  Encode.bytes opcode ++ Encode.imm32Bytes (takenAddress - after).toUInt32

/-- All generated cases. Memory forms point their base register at the data
page (or deliberately at an unmapped address), so the model and processor see
the same mapped window. -/
def cases : Array Case := Id.run do
  let mut out : Array Case := #[]
  let mut n := 0
  let add (out : Array Case) (n : Nat) (id : String) (code : ByteArray)
      (registers : Array Word) (writes := false) : Array Case :=
    out.push
      { id := s!"{id}.{n}", code := code, registers := registers, writes := writes,
        flags := (next (n.toUInt64 + 7)) &&& 0x8c1, seed := n.toUInt64 * 0x9e37 + 11 }
  -- Register and immediate moves.
  for w in widths do
    for d in gprs do
      for s in gprs do
        n := n + 1
        out := add out n "mov-rr" (Encode.encodeMov w d (.reg s)) (registersFor n)
      for v in edges do
        n := n + 1
        out := add out n "mov-ri" (Encode.encodeMov w d (.imm v)) (registersFor n)
  -- Loads, stores and lea through base/index/scale/disp32 addresses.
  let bases : Array GPR := #[.rax, .rbx, .rbp, .rsp, .r12, .r13, .r15]
  let indexRegs : Array (Option IndexReg) := #[none, some .rcx, some .rsi, some .r9, some .r14]
  let scales : Array Scale := #[.one, .two, .four, .eight]
  let displacements : Array UInt32 := #[0, 8, 0xfffffff8, 0x100]
  for w in widths do
    for b in bases do
      for i in indexRegs do
        for s in scales do
          for disp in displacements do
            let address : MemAddr := { base := some b, index := i, scale := s, displacement := disp }
            n := n + 1
            let mut regs := registersFor n
            let baseValue := if b == .rsp then stackTop else dataPage + 0x400
            regs := regs.set! ((registerOrder.findIdx? (· == b)).getD 0) baseValue
            if let some ix := i then
              regs := regs.set! ((registerOrder.findIdx? (· == ix.gpr)).getD 0) (n.toUInt64 % 16)
            let destination := gprs[n % 16]!
            out := add out n "load" (Encode.encodeLoad w destination address) regs
            out := add out n "store" (Encode.encodeStore w address destination) regs (writes := true)
            if w == .w64 then
              out := add out n "lea" (Encode.encodeLea destination address) regs
  -- Faulting accesses: an address in no mapped page.
  for w in widths do
    n := n + 1
    let regs := (registersFor n).set! 3 0x40300000
    let address : MemAddr := { base := some .rbx }
    out := add out n "load-fault" (Encode.encodeLoad w .rax address) regs
    out := add out n "store-fault" (Encode.encodeStore w address .rax) regs (writes := true)
  -- ALU register and immediate forms, and two-operand imul.
  for op in aluOps do
    for w in widths do
      for d in gprs do
        for k in [:4] do
          n := n + 1
          out := add out n "alu-rr" (Encode.encodeAlu op w d (.reg gprs[(n + k) % 16]!)) (registersFor n)
          out := add out n "alu-ri" (Encode.encodeAlu op w d (.imm (edges[(n + k) % edges.size]!).toUInt32)) (registersFor n)
  for mw in #[MulWidth.w16, .w32, .w64] do
    for d in gprs do
      for s in gprs do
        n := n + 1
        out := add out n "imul" (Encode.encodeImul mw d s) (registersFor n)
  -- Compare and conditional branch to the taken exit.
  for w in widths do
    for c in conditions do
      for k in [:12] do
        n := n + 1
        let left := gprs[n % 16]!
        let right : AluSource := if k % 2 == 0 then .reg gprs[(n + 5) % 16]!
          else .imm (edges[(n + k) % edges.size]!).toUInt32
        let compare := Encode.encodeCompare { width := w, left, right }
        let after := testAddress + compare.size.toUInt64 + 6
        out := add out n "cmp-jcc" (compare ++ rel32 [0x0f, Encode.nearOpcode c] after) (registersFor n)
  -- Stack and control forms.
  for r in gprs do
    n := n + 1
    out := add out n "push" (Encode.encodePush r) (registersFor n) (writes := true)
    n := n + 1
    out := add out n "pop" (Encode.encodePop r) (registersFor n)
  n := n + 1
  out := add out n "jmp" (rel32 [0xe9] (testAddress + 5)) (registersFor n)
  n := n + 1
  out := add out n "call" (rel32 [0xe8] (testAddress + 5)) (registersFor n) (writes := true)
  n := n + 1
  out := add out n "ret" (Encode.encodeMov .w64 .r11 (.imm takenAddress) ++
    Encode.encodePush .r11 ++ Encode.bytes [0xc3]) (registersFor n) (writes := true)
  return out

/-! ## Independent decoding with LLVM

Every case is decoded by `llvm-mc`, with a `ud2` separator between cases.
Each case must produce exactly the instruction sequence the local decoder
sees (so lengths agree), with the same mnemonics and no invalid encodings. -/

def aluName : AluOp → String
  | .add => "add" | .sub => "sub" | .and => "and" | .or => "or" | .xor => "xor"

def conditionName : Condition → String
  | .eq => "je" | .ne => "jne" | .unsignedLt => "jb" | .unsignedLe => "jbe"
  | .unsignedGt => "ja" | .unsignedGe => "jae" | .signedLt => "jl" | .signedLe => "jle"
  | .signedGt => "jg" | .signedGe => "jge"

/-- Mnemonics LLVM may print for a decoded operation. -/
def mnemonics : Decode.Operation → List String
  | .mov _ _ (.imm _) => ["mov", "movabs"]
  | .mov .. => ["mov"]
  | .load .w8 .. | .load .w16 .. => ["movzx"]
  | .load .. | .store .. => ["mov"]
  | .lea .. => ["lea"]
  | .alu op .. => [aluName op]
  | .imul .. => ["imul"]
  | .compare .. => ["cmp"]
  | .push _ => ["push"]
  | .pop _ => ["pop"]
  | .call _ => ["call"]
  | .jump _ => ["jmp"]
  | .branch condition _ => [conditionName condition]
  | .ret => ["ret"]

/-- The local decoder's operation sequence for a case's bytes. -/
def localOperations (code : ByteArray) : Except String (List Decode.Operation) := do
  let rec go : Nat → List UInt8 → Except String (List Decode.Operation)
    | _, [] => pure []
    | 0, _ => throw "too many operations"
    | fuel + 1, input => do
      let some (operation, rest) := Decode.one input | throw "local decoder rejected case bytes"
      return operation :: (← go fuel rest)
  go 8 code.data.toList

def llvmInput (c : Case) : String :=
  " ".intercalate (c.code.data.toList.map fun b => s!"0x{hexNat b.toNat}") ++ "\n0x0f 0x0b\n"

/-- Decode every case with `llvm-mc` and compare mnemonic sequences. -/
def checkLlvm (llvmMc : String) : IO Nat := do
  let input := String.join (cases.toList.map llvmInput)
  let output ← IO.FS.withTempFile fun handle path => do
    handle.putStr input
    handle.flush
    IO.Process.output { cmd := llvmMc, args := #["--disassemble", "-triple=x86_64",
      "-output-asm-variant=1", path.toString] }
  need (output.exitCode == 0 && !output.stderr.contains "invalid")
    s!"llvm-mc rejected an encoding: {output.stderr.take 400}"
  let names := (output.stdout.splitOn "\n").filterMap fun line =>
    match (line.trimAscii.toString.splitOn "\t").filter (· != "") with
    | name :: _ => if name.startsWith "." then none else some name
    | [] => none
  let groups := (names.foldl (init := (([] : List (List String)), ([] : List String)))
    fun (done, current) name =>
      if name == "ud2" then (current.reverse :: done, []) else (done, name :: current)).1.reverse
    |>.filter (!·.isEmpty)
  need (groups.length == cases.size) s!"llvm-mc produced {groups.length} of {cases.size} cases"
  for (c, group) in cases.toList.zip groups do
    let expected ← checked (localOperations c.code)
    need (expected.length == group.length &&
        (expected.zip group).all fun (operation, name) => (mnemonics operation).contains name)
      s!"{c.id}: llvm-mc decodes {group}, local decoder {expected.map mnemonics}"
  return cases.size

end CheckX86Hardware

open CheckX86Hardware in
def main (args : List String) : IO UInt32 := cli "x86 hardware-differential check failed" do
  let args ← checked (parseArgs ["--harness", "--llvm-mc"] args)
  let some harness := optional args "--harness"
    | throw (IO.userError "usage: check-x86-hardware --harness PATH (a compiled hw_diff_harness)")
  let input := String.intercalate "\n" (cases.toList.map Case.line) ++ "\n"
  let output ← IO.FS.withTempFile fun handle path => do
    handle.putStr input
    handle.flush
    IO.Process.output { cmd := "sh", args := #["-c", "exec \"$0\" < \"$1\"", harness, path.toString] }
  need (output.exitCode == 0) s!"harness exited with {output.exitCode}: {output.stderr}"
  let text := output.stdout
  let lines := (text.splitOn "\n").filter (· != "")
  need (lines.headD "" == "layout 40000800 40000c00 40100000 40200000")
    s!"harness layout differs: {lines.headD ""}"
  let results := lines.drop 1
  need (results.length == cases.size) s!"harness returned {results.length} of {cases.size} cases"
  let mut failures := 0
  let mut faults := 0
  for (c, line) in cases.toList.zip results do
    let (id, native) ← checked (parseNative line)
    need (id == c.id) s!"harness order: expected {c.id}, got {id}"
    if native.isNone then faults := faults + 1
    let errors ← checked (compare c native)
    unless errors.isEmpty do
      failures := failures + 1
      if failures ≤ 20 then IO.eprintln s!"{c.id} [{c.line}]: {errors}"
  need (failures == 0) s!"{failures} of {cases.size} cases disagree with the processor"
  let decoded ← match optional args "--llvm-mc" with
    | some llvmMc => pure s!"; llvm-mc decodes all {← checkLlvm llvmMc} identically"
    | none => pure ""
  IO.println s!"x86 hardware-differential check ok: {cases.size} cases ({faults} expected faults) agree with the host processor{decoded}"
