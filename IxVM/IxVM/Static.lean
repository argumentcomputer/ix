import IxVM.Program
import Aiur.Generic.StaticTableFacts

/-! # The prepared source's static tables

`coreTables` is what static preparation (`Aiur.Generic.staticProgram`) makes
of the prepared program's tables: the byte tables of the generator
(`Aiur.Library.U8.tables`, `coreTables_generator`), rows as constants, row and
map types in the core type language. `tablesChecked` is the proof a
`Generic.Source` carries that they typecheck. It is proved from the
generator, not by evaluating the 526,592 rows: every row has its table's row
type, and the input rows of every map are distinct (the generator's inputs
are distinct naturals below the field's characteristic). The test suite
`ixvm-source` checks that `coreTables` is the native preparation's. -/

open private literal pair byteTy from Aiur.Library.U8

set_option maxRecDepth 10000

namespace IxVM
open Aiur.Generic

/-- A generated table cell over `F`, as a constant. -/
def coreLeaf : Expr Nat → Aiur.Constant F
  | .literal x => .field (x : F)
  | _ => .tuple []

/-- A generated table row over `F`, as static preparation makes it a constant. -/
def coreRow : Expr Nat → Aiur.Constant F
  | .literal x => .field (x : F)
  | .tuple xs => .tuple (xs.map coreLeaf)
  | .array xs => .tuple (xs.map coreLeaf)
  | _ => .tuple []

/-- The byte pairs the pair tables range over. -/
def pairInputs : List (Nat × Nat) :=
  (List.range 256).flatMap fun a => (List.range 256).map fun b => (a, b)

/-- The sums the carry tables range over, with their low bytes. -/
def sumPairs : List (Nat × Nat) := Aiur.Library.Carry.rows 256 768

/-- `Aiur.Library.U8.tables`, its `let`s unfolded. -/
theorem u8Tables_eq : Aiur.Library.U8.tables = [
    ⟨"byte_inputs", .tuple [.field], (List.range 256).map fun x => .tuple [.literal x]⟩,
    ⟨"byte_values", .named "U8" [], (List.range 256).map fun x => .literal x⟩,
    ⟨"byte_bits", .array .field 8, (List.range 256).map fun x =>
      .array ((List.range 8).map fun i => .literal ((x / 2^i) % 2))⟩,
    ⟨"pair_inputs", .tuple [.field, .field], pairInputs.map fun (a,b) =>
      .tuple [.literal a, .literal b]⟩,
    ⟨"pair_units", .tuple [], pairInputs.map fun _ => .tuple []⟩,
    ⟨"pair_xors", .named "U8" [], pairInputs.map fun (a,b) => .literal (Nat.xor a b)⟩,
    ⟨"pair_adds", .tuple [.named "U8" [], .named "U8" []], pairInputs.map fun (a,b) =>
      .tuple [.literal ((a+b)%256), .literal ((a+b)/256)]⟩,
    ⟨"pair_subs", .tuple [.named "U8" [], .named "U8" []], pairInputs.map fun (a,b) =>
      .tuple [.literal ((a+256-b)%256), .literal (if a < b then 1 else 0)]⟩,
    ⟨"pair_muls", .tuple [.named "U8" [], .named "U8" []], pairInputs.map fun (a,b) =>
      .tuple [.literal ((a*b)%256), .literal ((a*b)/256)]⟩,
    ⟨"pair_xor_parts4", .named "Parts4" [], pairInputs.map fun (a,b) =>
      .tuple [.literal (Nat.xor a b / 16), .literal ((Nat.xor a b % 16) * 16)]⟩,
    ⟨"pair_xor_parts7", .named "Parts7" [], pairInputs.map fun (a,b) =>
      .tuple [.literal (Nat.xor a b / 128), .literal ((Nat.xor a b % 128) * 2)]⟩,
    ⟨"sum_inputs", .tuple [.field], sumPairs.map fun (n, _) => .tuple [.literal n]⟩,
    ⟨"sum_bytes", .named "U8" [], sumPairs.map fun (_, b) => .literal b⟩] := rfl

/-! ## The tables -/

def byteInputsTable : Aiur.Table F where
  name := "UInt8::" ++ "byte_inputs"
  rowType := (Ty.tuple [.field]).toCore
  rows := ((List.range 256).map fun x => .tuple [.literal x]).map coreRow

def byteValuesTable : Aiur.Table F where
  name := "UInt8::" ++ "byte_values"
  rowType := Ty.field.toCore
  rows := ((List.range 256).map fun x => .literal x).map coreRow

def byteBitsTable : Aiur.Table F where
  name := "UInt8::" ++ "byte_bits"
  rowType := (Ty.array .field 8).toCore
  rows := ((List.range 256).map fun x => .array ((List.range 8).map fun i => .literal ((x / 2^i) % 2))).map coreRow

def pairInputsTTable : Aiur.Table F where
  name := "UInt8::" ++ "pair_inputs"
  rowType := (Ty.tuple [.field, .field]).toCore
  rows := (pairInputs.map fun (a,b) => .tuple [.literal a, .literal b]).map coreRow

def pairUnitsTable : Aiur.Table F where
  name := "UInt8::" ++ "pair_units"
  rowType := (Ty.tuple []).toCore
  rows := (pairInputs.map fun _ => .tuple []).map coreRow

def pairXorsTable : Aiur.Table F where
  name := "UInt8::" ++ "pair_xors"
  rowType := Ty.field.toCore
  rows := (pairInputs.map fun (a,b) => .literal (Nat.xor a b)).map coreRow

def pairAddsTable : Aiur.Table F where
  name := "UInt8::" ++ "pair_adds"
  rowType := (Ty.tuple [.field, .field]).toCore
  rows := (pairInputs.map fun (a,b) => .tuple [.literal ((a+b)%256), .literal ((a+b)/256)]).map coreRow

def pairSubsTable : Aiur.Table F where
  name := "UInt8::" ++ "pair_subs"
  rowType := (Ty.tuple [.field, .field]).toCore
  rows := (pairInputs.map fun (a,b) => .tuple [.literal ((a+256-b)%256), .literal (if a < b then 1 else 0)]).map coreRow

def pairMulsTable : Aiur.Table F where
  name := "UInt8::" ++ "pair_muls"
  rowType := (Ty.tuple [.field, .field]).toCore
  rows := (pairInputs.map fun (a,b) => .tuple [.literal ((a*b)%256), .literal ((a*b)/256)]).map coreRow

def pairXorParts4Table : Aiur.Table F where
  name := "UInt8::" ++ "pair_xor_parts4"
  rowType := (Ty.tuple [.field, .field]).toCore
  rows := (pairInputs.map fun (a,b) => .tuple [.literal (Nat.xor a b / 16), .literal ((Nat.xor a b % 16) * 16)]).map coreRow

def pairXorParts7Table : Aiur.Table F where
  name := "UInt8::" ++ "pair_xor_parts7"
  rowType := (Ty.tuple [.field, .field]).toCore
  rows := (pairInputs.map fun (a,b) => .tuple [.literal (Nat.xor a b / 128), .literal ((Nat.xor a b % 128) * 2)]).map coreRow

def sumInputsTable : Aiur.Table F where
  name := "UInt8::" ++ "sum_inputs"
  rowType := (Ty.tuple [.field]).toCore
  rows := (sumPairs.map fun (n, _) => .tuple [.literal n]).map coreRow

def sumBytesTable : Aiur.Table F where
  name := "UInt8::" ++ "sum_bytes"
  rowType := Ty.field.toCore
  rows := (sumPairs.map fun (_, b) => .literal b).map coreRow

def coreTableList : List (Aiur.Table F) :=
  [byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

/-- The prepared source's static table program. -/
def coreTables : Aiur.Program F where
  functions := []
  tables := coreTableList
  maps := maps.map fun m =>
    { name := m.name, params := m.params.map fun (n, t) => (n, t.toCore),
      result := m.result.toCore, input := m.input, output := m.output }

/-- **The tables are the generator's**, made constants. -/
theorem coreTables_generator : coreTables.tables =
    (Aiur.Library.U8.tables.zip tableRowTypes).map fun (t, rowType) =>
      { name := "UInt8::" ++ t.name, rowType := rowType.toCore, rows := t.rows.map coreRow } := by
  rw [u8Tables_eq]
  rfl

/-! ## Rows -/

/-- A row type made of fields only, as every byte table's is. -/
def FieldsOnly : Aiur.Ty → Prop
  | .field => True
  | .tuple ts => ∀ t ∈ ts, t = .field
  | _ => False

theorem checkNames_fieldsOnly (decls : Aiur.Declarations) :
    ∀ t : Aiur.Ty, FieldsOnly t → t.checkNames decls = .ok ()
  | .field, _ => by simp [Aiur.Ty.checkNames]
  | .tuple ts, h => by
    unfold Aiur.Ty.checkNames
    exact Aiur.forIn_ok_of fun t ht => by rw [h t ht]; simp [Aiur.Ty.checkNames]
  | .ptr _, h | .enum _, h => h.elim

theorem table_ok (table : Aiur.Table F) (fields : FieldsOnly table.rowType)
    (free : table.rowType.pointerFree [] = true)
    (rows : ∀ row ∈ table.rows, row.type = table.rowType ∧ row.wellFormed [] = true) :
    Aiur.checkTable coreTables table = .ok () :=
  Aiur.checkTable_ok_of (checkNames_fieldsOnly _ _ fields) free rows

theorem tables_ok : ∀ table ∈ coreTables.tables, Aiur.checkTable coreTables table = .ok () := by
  intro table member
  simp only [coreTables, coreTableList, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply table_ok
    · simp [FieldsOnly, Ty.toCore, byteInputsTable, byteValuesTable, byteBitsTable,
        pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable,
        pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]
    · decide +kernel
    · intro row member
      simp only [byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable,
        pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable,
        pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable,
        List.map_map, List.mem_map, Function.comp] at member ⊢
      obtain ⟨x, -, rfl⟩ := member
      simp [coreRow, coreLeaf, Aiur.Value.type, Aiur.Value.wellFormed, Ty.toCore, List.map_map,
        Function.comp_def]

/-! ## Distinct inputs -/

theorem natCast_inj {a b : Nat} (ha : a < 1024) (hb : b < 1024) (h : (a : F) = (b : F)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  have hm : (1024 : Nat) ≤ Aiur.Library.U32.Goldilocks.modulus := by
    simp only [Aiur.Library.U32.Goldilocks.modulus]; omega
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h

theorem byteInputs_nodup : byteInputsTable.rows.Nodup := by
  simp only [byteInputsTable, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro x hx y hy h
  simp only [List.mem_range] at hx hy
  simp only [Function.comp, coreRow, coreLeaf, List.map, Aiur.Value.tuple.injEq,
    List.cons.injEq, Aiur.Value.field.injEq, and_true] at h
  exact natCast_inj (by omega) (by omega) h

theorem sumInputs_nodup : sumInputsTable.rows.Nodup := by
  simp only [sumInputsTable, sumPairs, Aiur.Library.Carry.rows, List.map_map]
  apply List.Nodup.map_on _ List.nodup_range
  intro x hx y hy h
  simp only [List.mem_range] at hx hy
  simp only [Function.comp, coreRow, coreLeaf, List.map, Aiur.Value.tuple.injEq,
    List.cons.injEq, Aiur.Value.field.injEq, and_true] at h
  exact natCast_inj (by omega) (by omega) h

theorem pairInputs_nodup : pairInputsTTable.rows.Nodup := by
  simp only [pairInputsTTable, List.map_map]
  apply List.Nodup.map_on
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
    simp only [pairInputs, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hp hq
    obtain ⟨a', ha, b', hb, rfl, rfl⟩ := hp
    obtain ⟨c', hc, d', hd, rfl, rfl⟩ := hq
    simp only [Function.comp, coreRow, coreLeaf, List.map, Aiur.Value.tuple.injEq,
      List.cons.injEq, Aiur.Value.field.injEq, and_true] at h
    rw [natCast_inj (by omega) (by omega) h.1, natCast_inj (by omega) (by omega) h.2]
  · unfold pairInputs
    rw [List.nodup_flatMap]
    refine ⟨fun a _ => List.nodup_range.map_on (fun x _ y _ h => by simpa using h), ?_⟩
    refine List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range]
    rintro _ ⟨x, _, rfl⟩ ⟨y, _, h⟩
    exact hab (Prod.mk.inj h).1.symm

/-! ## Maps -/

theorem find_byteInputs : coreTables.findTable? "UInt8::byte_inputs" = some byteInputsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_byteValues : coreTables.findTable? "UInt8::byte_values" = some byteValuesTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_byteBits : coreTables.findTable? "UInt8::byte_bits" = some byteBitsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairInputsT : coreTables.findTable? "UInt8::pair_inputs" = some pairInputsTTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairUnits : coreTables.findTable? "UInt8::pair_units" = some pairUnitsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairXors : coreTables.findTable? "UInt8::pair_xors" = some pairXorsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairAdds : coreTables.findTable? "UInt8::pair_adds" = some pairAddsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairSubs : coreTables.findTable? "UInt8::pair_subs" = some pairSubsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairMuls : coreTables.findTable? "UInt8::pair_muls" = some pairMulsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairXorParts4 : coreTables.findTable? "UInt8::pair_xor_parts4" = some pairXorParts4Table := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_pairXorParts7 : coreTables.findTable? "UInt8::pair_xor_parts7" = some pairXorParts7Table := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_sumInputs : coreTables.findTable? "UInt8::sum_inputs" = some sumInputsTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem find_sumBytes : coreTables.findTable? "UInt8::sum_bytes" = some sumBytesTable := by
  simp [coreTables, coreTableList, Aiur.Program.findTable?, byteInputsTable, byteValuesTable, byteBitsTable, pairInputsTTable, pairUnitsTable, pairXorsTable, pairAddsTable, pairSubsTable, pairMulsTable, pairXorParts4Table, pairXorParts7Table, sumInputsTable, sumBytesTable]

theorem maps_ok : ∀ map ∈ coreTables.maps, Aiur.checkMap coreTables map = .ok () := by
  intro map member
  simp only [coreTables, maps, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member

  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_byteInputs find_byteValues (by decide +kernel)
      (by decide +kernel) (by simp [byteInputsTable, byteValuesTable]) byteInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_byteInputs find_byteBits (by decide +kernel)
      (by decide +kernel) (by simp [byteInputsTable, byteBitsTable]) byteInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairUnits (by decide +kernel)
      (by decide +kernel) (by simp [pairInputsTTable, pairUnitsTable]) pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairXors (by decide +kernel)
      (by decide +kernel) (by simp [pairInputsTTable, pairXorsTable]) pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairAdds (by decide +kernel)
      (by decide +kernel) (by simp [pairInputsTTable, pairAddsTable]) pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairSubs (by decide +kernel)
      (by decide +kernel) (by simp [pairInputsTTable, pairSubsTable]) pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairMuls (by decide +kernel)
      (by decide +kernel) (by simp [pairInputsTTable, pairMulsTable]) pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairXorParts4
      (by decide +kernel) (by decide +kernel) (by simp [pairInputsTTable, pairXorParts4Table])
      pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_pairInputsT find_pairXorParts7
      (by decide +kernel) (by decide +kernel) (by simp [pairInputsTTable, pairXorParts7Table])
      pairInputs_nodup
  · exact Aiur.checkMap_ok_of (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) find_sumInputs find_sumBytes (by decide +kernel)
      (by decide +kernel) (by simp [sumInputsTable, sumBytesTable]) sumInputs_nodup

/-- **The static tables typecheck**, the obligation `Generic.Source` carries. -/
theorem tablesChecked : Aiur.typecheck coreTables = .ok () :=
  Aiur.typecheck_ok_of rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    tables_ok maps_ok

end IxVM
