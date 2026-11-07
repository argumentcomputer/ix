import IxCC.X86.Table.Rows

/-!
# The decoder's row index

The decoder finds a row from the bytes it has parsed: the operand-size
prefix, REX.W, the opcode map, the opcode byte and, for group opcodes, the
ModRM.reg digit. `Table.index` expands every row to these keys (eight
opcode bytes for register-in-opcode rows) and `Table.lookup` searches it.

The facts below are kernel-evaluated `Bool` checks (`decide`, never
`native_decide`): keys are distinct, every row is found from its own
encoding, and every row's descriptor has the operand layout of its encoding
class. They say nothing about whether a row's opcode is the one the
processor uses; the hardware and LLVM gates test that.
-/

namespace IxCC.X86

def OpMap.code : OpMap → Nat
  | .legacy => 0
  | .x0F => 1

/-- The ModRM.reg digit of a group row; 8 when the row has none. -/
def EncDesc.digit (enc : EncDesc) : Nat :=
  match enc.modrm with
  | .digit value => value
  | .none | .reg => 8

/-- The opcode bytes a row occupies: eight for register-in-opcode rows. -/
def EncDesc.opcodes (enc : EncDesc) : List UInt8 :=
  match enc.emb with
  | .regLow3 => (List.range 8).map fun low => enc.opcode + UInt8.ofNat low
  | .none => [enc.opcode]

namespace Table

/-- One decoder key: prefix, REX.W, map, opcode byte and digit (8: none). -/
def key (p66 rexW : Bool) (map : OpMap) (opcode : UInt8) (digit : Nat) : Nat :=
  ((((if p66 then 2 else 0) + (if rexW then 1 else 0)) * 2 + map.code) * 256 + opcode.toNat) * 9 + digit

def rowKeys (o : Op) : List Nat :=
  let enc := (desc o).enc
  enc.opcodes.map fun opcode => key enc.p66 enc.rexW enc.map opcode enc.digit

/-- Every row under each of its keys. -/
def index : List (Nat × Op) :=
  Op.rows.flatMap fun o => (rowKeys o).map fun k => (k, o)

def lookup (k : Nat) : Option Op :=
  (index.find? fun entry => entry.1 == k).map (·.2)

/-- A row is found from its own bytes: a plain row by its opcode alone; a
group row only once its ModRM digit is known. -/
def reachable (o : Op) : Bool :=
  let enc := (desc o).enc
  enc.opcodes.all fun opcode =>
    match enc.modrm with
    | .digit value =>
        decide (value < 8) && lookup (key enc.p66 enc.rexW enc.map opcode 8) == none &&
          lookup (key enc.p66 enc.rexW enc.map opcode value) == some o
    | .none | .reg => lookup (key enc.p66 enc.rexW enc.map opcode 8) == some o

/-- An opcode byte is not mistaken for a prefix or the two-byte escape. -/
def opcodeClear (map : OpMap) (opcode : UInt8) : Bool :=
  match map with
  | .x0F => true
  | .legacy => opcode != 0x66 && opcode != 0x0f && !(0x40 ≤ opcode.toNat && opcode.toNat < 0x50)

def rmKinds (slot : Slot) : Bool :=
  slot.kinds == [.reg, .mem] || slot.kinds == [.mem]

def regKinds (slot : Slot) : Bool := slot.kinds == [.reg]

def immKinds (kind : ImmKind) (slot : Slot) : Bool :=
  match kind with
  | .imm8 => slot.kinds == [.imm8]
  | .imm16 => slot.kinds == [.imm16]
  | .imm32 => slot.kinds == [.imm32] || slot.kinds == [.rel32]
  | .imm64 => slot.kinds == [.imm64]
  | .none => false

/-- The descriptor has the operand layout of the row's encoding class. -/
def shaped (o : Op) : Bool :=
  let d := desc o
  let enc := d.enc
  enc.opcodes.all (opcodeClear enc.map) &&
  (enc.emb != .regLow3 || (enc.opcode.toNat % 8 == 0 && enc.opcode.toNat < 248)) &&
  match o.form, d.slots with
  | .MR, [rm, reg] =>
      enc.modrm == .reg && enc.emb == .none && enc.imm == .none && rmKinds rm && regKinds reg
  | .RM, [reg, rm] =>
      enc.modrm == .reg && enc.emb == .none && enc.imm == .none && regKinds reg && rmKinds rm
  | .MI, [rm, imm] | .MI8, [rm, imm] =>
      enc.modrm != .none && enc.modrm != .reg && enc.emb == .none && rmKinds rm && immKinds enc.imm imm
  | .M, [rm] | .MC, [rm] =>
      enc.modrm != .none && enc.modrm != .reg && enc.emb == .none && enc.imm == .none && rmKinds rm
  | .OI, [reg, imm] =>
      enc.modrm == .none && enc.emb == .regLow3 && regKinds reg && immKinds enc.imm imm
  | .O, [reg] =>
      enc.modrm == .none && enc.emb == .regLow3 && enc.imm == .none && regKinds reg
  | .RMI, [reg, rm, imm] | .RMI8, [reg, rm, imm] =>
      enc.modrm == .reg && enc.emb == .none && regKinds reg && rmKinds rm && immKinds enc.imm imm
  | .D32, [rel] =>
      enc.modrm == .none && enc.emb == .none && enc.imm == .imm32 && rel.kinds == [.rel32]
  | .ZO, [] => enc.modrm == .none && enc.emb == .none && enc.imm == .none
  | _, _ => false

/-- The longest encoding a row can have: prefixes, map, opcode, ModRM with
SIB and disp32, and the immediate. -/
def maxLength (o : Op) : Nat :=
  let enc := (desc o).enc
  (if enc.p66 then 1 else 0) + 1 + (if enc.map == .x0F then 1 else 0) + 1 +
    (if enc.modrm == .none then 0 else 6) + enc.imm.bytes

end Table

/-- Every row fits the architectural fifteen-byte instruction limit. -/
theorem table_bounded : Op.rows.all (fun o => decide (Table.maxLength o ≤ 15)) = true := by decide

set_option maxRecDepth 8192 in
/-- The index keys are pairwise distinct: the decoder is deterministic. -/
theorem table_injective : (Table.index.map (·.1)).Nodup := by decide

set_option maxRecDepth 8192 in
/-- Every row is found by the decoder from its own encoding fields. -/
theorem table_reachable : Op.rows.all Table.reachable = true := by decide

set_option maxRecDepth 8192 in
/-- Every row's slots match its encoding class. -/
theorem table_shaped : Op.rows.all Table.shaped = true := by decide

theorem Op.reachable_of_row {o : Op} (row : o ∈ Op.rows) : Table.reachable o = true :=
  List.all_eq_true.mp table_reachable o row

theorem Op.shaped_of_row {o : Op} (row : o ∈ Op.rows) : Table.shaped o = true :=
  List.all_eq_true.mp table_shaped o row

end IxCC.X86
